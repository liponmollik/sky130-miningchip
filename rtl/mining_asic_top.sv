// ============================================================================
// 1 TH/s Cryptocurrency Mining ASIC – SystemVerilog RTL (SKY130 compatible)
// -----------------------------------------------------------------------------
// This single SystemVerilog file contains a hierarchical RTL scaffold that
// follows the Grand → Child → Grand‑child architecture described in the
// Project Requirement Specification.
//
//  * mining_top           – Top‑level ("Grand") dispatcher and host interface
//  * child_unit           – Intermediate ("Child") job splitter & result collector
//  * hash_core            – Pipelined SHA‑256 engine ("Grand‑child")
//  * sha256_round_func    – Pure combinational SHA‑256 round function
//
// NOTE: The code is written to be synthesizable with the open‑source Yosys
//       toolchain. Timing and power optimisation will be addressed during
//       synthesis and place‑and‑route.
//
// TODO markers indicate areas where extra optimisation or feature work can
//       be added as the project matures.
// ============================================================================
`timescale 1ns/1ps

// -----------------------------------------------------------------------------
// Configuration package – central location for global parameters
// -----------------------------------------------------------------------------
package mining_cfg_pkg;
  // -------------------------------------------------------------------------
  // Architectural parameters – tune these based on frequency & area targets
  // -------------------------------------------------------------------------
  parameter int unsigned NUM_CHILDREN      = 4;           // # of child units
  parameter int unsigned CORES_PER_CHILD  = 64;          // hash_cores per child
  parameter int unsigned CORE_PIPE_DEPTH  = 4;           // SHA‑256 pipeline depth
  
  // Target clock frequency (for STA guidance only)
  parameter int unsigned TARGET_CLK_MHZ   = 500;

  // Host register mapping (simple example)
  typedef enum int unsigned {
    REG_JOB_LO      = 0,  // bits 31:0 of 512‑bit job block (little endian)
    REG_JOB_HI      = 15, // bits 511:480
    REG_NONCE_START = 16,
    REG_NONCE_END   = 17,
    REG_CTRL        = 18,
    REG_STATUS      = 19
  } reg_addr_e;
endpackage : mining_cfg_pkg

import mining_cfg_pkg::*;

// -----------------------------------------------------------------------------
// sha256_round_func – combinational round function (one of 64 rounds)
// -----------------------------------------------------------------------------
module sha256_round_func (
  input  logic [31:0] a, b, c, d, e, f, g, h,
  input  logic [31:0] k_const,
  input  logic [31:0] w_t,
  output logic [31:0] a_out, b_out, c_out, d_out, e_out, f_out, g_out, h_out
);
  // SHA‑256 helper functions
  function automatic logic [31:0] Ch (input logic [31:0] x, y, z);
    Ch = (x & y) ^ (~x & z);
  endfunction
  function automatic logic [31:0] Maj (input logic [31:0] x, y, z);
    Maj = (x & y) ^ (x & z) ^ (y & z);
  endfunction
  function automatic logic [31:0] ROTR (input int unsigned s, input logic [31:0] x);
    ROTR = (x >> s) | (x << (32 - s));
  endfunction
  function automatic logic [31:0] SIGMA0 (input logic [31:0] x);
    SIGMA0 = ROTR(2, x) ^ ROTR(13, x) ^ ROTR(22, x);
  endfunction
  function automatic logic [31:0] SIGMA1 (input logic [31:0] x);
    SIGMA1 = ROTR(6, x) ^ ROTR(11, x) ^ ROTR(25, x);
  endfunction
  function automatic logic [31:0] sigma0 (input logic [31:0] x);
    sigma0 = ROTR(7, x) ^ ROTR(18, x) ^ (x >> 3);
  endfunction
  function automatic logic [31:0] sigma1 (input logic [31:0] x);
    sigma1 = ROTR(17, x) ^ ROTR(19, x) ^ (x >> 10);
  endfunction

  // Compression function calculations
  logic [31:0] t1, t2;
  always_comb begin
    t1 = h + SIGMA1(e) + Ch(e, f, g) + k_const + w_t;
    t2 = SIGMA0(a) + Maj(a, b, c);
    a_out = t1 + t2;
    b_out = a;
    c_out = b;
    d_out = c;
    e_out = d + t1;
    f_out = e;
    g_out = f;
    h_out = g;
  end
endmodule : sha256_round_func

// -----------------------------------------------------------------------------
// hash_core – deeply pipelined SHA‑256 engine
// -----------------------------------------------------------------------------
module hash_core #(
  parameter PIPE_DEPTH = CORE_PIPE_DEPTH
) (
  input  logic            clk,
  input  logic            rst_n,
  // Job input (512‑bit block + starting nonce)
  input  logic [511:0]    block_in,
  input  logic            block_valid,
  output logic            block_ready,
  // Nonce injection
  input  logic [31:0]     nonce_in,
  input  logic            nonce_valid,
  output logic            nonce_ready,
  // Result output
  output logic [255:0]    hash_out,
  output logic [31:0]     nonce_out,
  output logic            hash_valid,
  input  logic            hash_ready
);
  // -------------------------------------------------------------------------
  // Internal registers & signals
  // -------------------------------------------------------------------------
  // Message schedule array W[0..63] – computed over several cycles.
  // For brevity, we model this as a simple dual‑port RAM. Optimise later.
  logic [31:0] W [0:63];

  // FSM state
  typedef enum logic [1:0] {IDLE, LOAD, COMPRESS, OUTPUT} core_state_e;
  core_state_e state, state_n;

  // TODO: Implement full message schedule loading and compression pipeline.
  // For now, provide a placeholder that asserts hash_valid after a fixed
  // latency, with a dummy hash value. Replace with full pipeline logic.

  logic [7:0] cycle_cnt;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state <= IDLE;
      cycle_cnt <= 0;
      hash_valid <= 0;
    end else begin
      state <= state_n;
      if (state == COMPRESS)
        cycle_cnt <= cycle_cnt + 1;
      else
        cycle_cnt <= 0;
      if (state == OUTPUT && hash_ready)
        hash_valid <= 0;
      else if (state == OUTPUT)
        hash_valid <= 1;
    end
  end

  always_comb begin
    // Default values
    state_n     = state;
    block_ready = 0;
    nonce_ready = 0;
    hash_out    = '0;
    nonce_out   = nonce_in;

    case (state)
      IDLE: begin
        block_ready = 1;
        nonce_ready = 1;
        if (block_valid && nonce_valid) begin
          state_n = COMPRESS;
        end
      end
      COMPRESS: begin
        if (cycle_cnt == (PIPE_DEPTH * 16)) begin // placeholder latency
          state_n = OUTPUT;
        end
      end
      OUTPUT: begin
        hash_out = 256'hDEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF_DEADBEEF;
        if (hash_ready) begin
          state_n = IDLE;
        end
      end
    endcase
  end
endmodule : hash_core

// -----------------------------------------------------------------------------
// child_unit – array of hash_cores with nonce distribution
// -----------------------------------------------------------------------------
module child_unit #(
  parameter int unsigned CORES = CORES_PER_CHILD
) (
  input  logic             clk,
  input  logic             rst_n,
  // Job block & nonce range from grand dispatcher
  input  logic [511:0]     job_block,
  input  logic             job_valid,
  output logic             job_ready,
  input  logic [31:0]      nonce_start,
  input  logic [31:0]      nonce_end,
  // Result upward
  output logic [255:0]     result_hash,
  output logic [31:0]      result_nonce,
  output logic             result_valid,
  input  logic             result_ready
);
  // -------------------------------------------------------------------------
  // Local signals
  // -------------------------------------------------------------------------
  localparam int unsigned NONCES_PER_CORE = (nonce_end - nonce_start + 1) / CORES;

  // Core arrays
  logic [CORES-1:0] core_block_ready, core_nonce_ready, core_hash_valid;
  logic [255:0]     core_hash_out [CORES-1:0];
  logic [31:0]      core_nonce_out[CORES-1:0];

  // Simple round‑robin nonce assignment (to improve later)
  genvar i;
  generate
    for (i = 0; i < CORES; i++) begin : g_hash_cores
      hash_core u_core (
        .clk          (clk),
        .rst_n        (rst_n),
        .block_in     (job_block),
        .block_valid  (job_valid),
        .block_ready  (core_block_ready[i]),
        .nonce_in     (nonce_start + i), // TODO: add nonce stride logic
        .nonce_valid  (job_valid),
        .nonce_ready  (core_nonce_ready[i]),
        .hash_out     (core_hash_out[i]),
        .nonce_out    (core_nonce_out[i]),
        .hash_valid   (core_hash_valid[i]),
        .hash_ready   (result_ready)
      );
    end
  endgenerate

  // Aggregate ready signals
  assign job_ready = &core_block_ready & &core_nonce_ready;

  // Simple OR‑reduction of valid hashes (one winner)
  integer j;
  always_comb begin
    result_valid = 0;
    result_hash  = '0;
    result_nonce = '0;
    for (j = 0; j < CORES; j++) begin
      if (core_hash_valid[j]) begin
        result_valid = 1;
        result_hash  = core_hash_out[j];
        result_nonce = core_nonce_out[j];
      end
    end
  end
endmodule : child_unit

// -----------------------------------------------------------------------------
// mining_top – grand dispatcher and host interface (simplified)
// -----------------------------------------------------------------------------
module mining_top #(
  parameter int unsigned NUM_CHILD = NUM_CHILDREN,
  parameter int unsigned CORES_PC  = CORES_PER_CHILD
) (
  input  logic            clk,
  input  logic            rst_n,
  // Simple host programming interface (placeholder)
  input  logic [511:0]    job_block_in,
  input  logic            job_block_valid,
  output logic            job_block_ready,
  input  logic [31:0]     nonce_range_start,
  input  logic [31:0]     nonce_range_end,
  input  logic            job_issue,
  // Result interface
  output logic [255:0]    winning_hash,
  output logic [31:0]     winning_nonce,
  output logic            winning_valid
);
  // -------------------------------------------------------------------------
  // Fan‑out job to children
  // -------------------------------------------------------------------------
  logic [NUM_CHILD-1:0] child_job_ready, child_result_valid;
  logic [255:0]         child_result_hash [NUM_CHILD-1:0];
  logic [31:0]          child_result_nonce[NUM_CHILD-1:0];

  genvar c;
  generate
    for (c = 0; c < NUM_CHILD; c++) begin : g_children
      child_unit #(.CORES(CORES_PC)) u_child (
        .clk           (clk),
        .rst_n         (rst_n),
        .job_block     (job_block_in),
        .job_valid     (job_issue),
        .job_ready     (child_job_ready[c]),
        .nonce_start   (nonce_range_start + (c * ((nonce_range_end - nonce_range_start) / NUM_CHILD))),
        .nonce_end     (nonce_range_start + ((c+1) * ((nonce_range_end - nonce_range_start) / NUM_CHILD)) - 1),
        .result_hash   (child_result_hash[c]),
        .result_nonce  (child_result_nonce[c]),
        .result_valid  (child_result_valid[c]),
        .result_ready  (1'b1) // always ready to accept result
      );
    end
  endgenerate

  assign job_block_ready = &child_job_ready;

  // OR‑reduce child results (first come first serve)
  integer k;
  always_comb begin
    winning_valid = 0;
    winning_hash  = '0;
    winning_nonce = '0;
    for (k = 0; k < NUM_CHILD; k++) begin
      if (child_result_valid[k]) begin
        winning_valid = 1;
        winning_hash  = child_result_hash[k];
        winning_nonce = child_result_nonce[k];
      end
    end
  end
endmodule : mining_top

// ============================================================================
// End of file – mining_asic_top.sv
// ============================================================================
