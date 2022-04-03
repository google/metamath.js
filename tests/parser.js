const Assert = require("assert");

describe("Parser", () => {
  it("Basic", () => {
  });
});


function assertThat(x) {
  return {
    equalsTo(y) {
      Assert.deepEqual(x, y);
    }
  }
}
