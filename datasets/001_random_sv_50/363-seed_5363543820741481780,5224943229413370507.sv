// Seed: 5363543820741481780,5224943229413370507

module oqih
  ( output wire logic [1:2][2:3][3:0][1:4] odijt [1:3][4:1]
  , output wire logic [1:0][2:0][4:1][1:2]  vz
  , output reg [2:4]  ixfx
  , output logic [0:3][0:1]  hcrkawb
  , input realtime vk
  , input trior logic [3:3][0:3][1:0][4:3]  itvadhot
  , input trior logic [4:2][4:4] dhcznf [0:0][4:0][4:0][3:1]
  );
  
  
  xor b(zhlfp, hcrkawb, vz);
  // warning: implicit conversion of port connection truncates from 8 to 1 bits
  //   logic [0:3][0:1]  hcrkawb -> logic hcrkawb
  //
  // warning: implicit conversion of port connection truncates from 48 to 1 bits
  //   wire logic [1:0][2:0][4:1][1:2]  vz -> logic vz
  
  xor ovae(zhlfp, itvadhot, itvadhot);
  // warning: implicit conversion of port connection truncates from 16 to 1 bits
  //   trior logic [3:3][0:3][1:0][4:3]  itvadhot -> logic itvadhot
  //
  // warning: implicit conversion of port connection truncates from 16 to 1 bits
  //   trior logic [3:3][0:3][1:0][4:3]  itvadhot -> logic itvadhot
  
  
  // Single-driven assigns
  assign hcrkawb = vz;
  assign ixfx = vz;
  
  // Multi-driven assigns
  assign odijt = odijt;
  assign vz = vz;
  assign dhcznf = dhcznf;
endmodule: oqih



// Seed after: 4926808626531518854,5224943229413370507
