include "casa.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "csubrg.mm"
include "cin.mm"
include "crab.mm"
include "cint.mm"
include "aspval.mm"
include "clmod.mm"
include "c0.mm"
include "wne.mm"
include "assalmod.mm"
include "adantr.mm"
include "ssrab2.mm"
include "inss2.mm"
include "sstri.mm"
include "a1i.mm"
include "cvv.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "intex.mm"
include "sylibr.mm"
include "lssintcl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem asplss
  let cA: class A
  let cS: class S
  let cL: class L
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vw: setvar w
  let cT: class T
  assume aspval.a: |- A = ( AlgSpan ` W )
  assume aspval.v: |- V = ( Base ` W )
  assume aspval.l: |- L = ( LSubSp ` W )


  assert |- ( ( W e. AssAlg /\ S C_ V ) -> ( A ` S ) e. L )

  proof
    cW
    casa
    wcel
    #
    cS
    cV
    wss
    #
    wa
    #
    cS
    cA
    cfv
    #
    cS
    vt
    cv
    wss
    #
    vt
    cW
    csubrg
    cfv
    #
    cL
    cin
    #
    crab
    #
    cint
    #
    cL
    vt
    cA
    cS
    cL
    cV
    cW
    aspval.a
    aspval.v
    aspval.l
    aspval
    #
    @2
    cW
    clmod
    wcel
    #
    @7
    cL
    wss
    #
    @7
    c0
    wne
    #
    @8
    cL
    wcel
    @0
    @10
    @1
    cW
    assalmod
    adantr
    @11
    @2
    @7
    @6
    cL
    @4
    vt
    @6
    ssrab2
    @5
    cL
    inss2
    sstri
    a1i
    @2
    @8
    cvv
    wcel
    @12
    @2
    @8
    @3
    cvv
    @9
    cS
    cA
    fvex
    syl6eqelr
    @7
    intex
    sylibr
    @7
    cL
    cW
    aspval.l
    lssintcl
    syl3anc
    eqeltrd
end
