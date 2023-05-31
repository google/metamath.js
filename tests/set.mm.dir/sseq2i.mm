include "wceq.mm";
include "wss.mm";
include "wb.mm";
include "sseq2.mm";
include "ax-mp.mm";

theorem sseq2i(cA: $class$ A, cB: $class$ B, cC: $class$ C) {
  assume sseq1i.1: $|- A = B$;





  do {
    cA;
    cB;
    wceq;
    cC;
    cA;
    wss;
    cC;
    cB;
    wss;
    wb;
    sseq1i.1;
    cA;
    cB;
    cC;
    sseq2;
    ax-mp;
  };

  return $|-$ $( C C_ A <-> C C_ B )$;
}
