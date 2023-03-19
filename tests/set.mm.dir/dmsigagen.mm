include "cvv.mm"
include "cv.mm"
include "wss.mm"
include "cuni.mm"
include "csiga.mm"
include "cfv.mm"
include "crab.mm"
include "cint.mm"
include "csigagen.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "wrex.mm"
include "cpw.mm"
include "vuniex.mm"
include "pwsiga.mm"
include "ax-mp.mm"
include "pwuni.mm"
include "sseq2.mm"
include "rspcev.mm"
include "mp2an.mm"
include "rabn0.mm"
include "mpbir.mm"
include "intex.mm"
include "mpbi.mm"
include "df-sigagen.mm"
include "dmmpti.mm"

theorem dmsigagen
  let vj: setvar j
  let vs: setvar s


  assert |- dom sigaGen = _V

  proof
    vj
    cvv
    vj
    cv
    #
    vs
    cv
    #
    wss
    #
    vs
    @0
    cuni
    #
    csiga
    cfv
    #
    crab
    #
    cint
    #
    csigagen
    @5
    c0
    wne
    #
    @6
    cvv
    wcel
    @7
    @2
    vs
    @4
    wrex
    #
    @3
    cpw
    #
    @4
    wcel
    #
    @0
    @9
    wss
    #
    @8
    @3
    cvv
    wcel
    @10
    vj
    vuniex
    @3
    cvv
    pwsiga
    ax-mp
    @0
    pwuni
    @2
    @11
    vs
    @9
    @4
    @1
    @9
    @0
    sseq2
    rspcev
    mp2an
    @2
    vs
    @4
    rabn0
    mpbir
    @5
    intex
    mpbi
    vj
    vs
    df-sigagen
    dmmpti
end
