include "wcel.mm"
include "c0.mm"
include "ctpos.mm"
include "wbr.mm"
include "cdm.mm"
include "ccnv.mm"
include "csn.mm"
include "cun.mm"
include "cuni.mm"
include "wa.mm"
include "brtpos2.mm"
include "ssun2.mm"
include "0ex.mm"
include "snid.mm"
include "sselii.mm"
include "biantrur.mm"
include "cnvsn0.mm"
include "unieqi.mm"
include "uni0.mm"
include "eqtri.mm"
include "breq1i.mm"
include "bitr3i.mm"
include "syl6bb.mm"

theorem brtpos0
  let cA: class A
  let cF: class F
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( A e. V -> ( (/) tpos F A <-> (/) F A ) )

  proof
    cA
    cV
    wcel
    c0
    cA
    cF
    ctpos
    wbr
    c0
    cF
    cdm
    ccnv
    #
    c0
    csn
    #
    cun
    #
    wcel
    #
    @1
    ccnv
    #
    cuni
    #
    cA
    cF
    wbr
    #
    wa
    #
    c0
    cA
    cF
    wbr
    #
    c0
    cA
    cF
    cV
    brtpos2
    @7
    @6
    @8
    @3
    @6
    @1
    @2
    c0
    @1
    @0
    ssun2
    c0
    0ex
    snid
    sselii
    biantrur
    @5
    c0
    cA
    cF
    @5
    c0
    cuni
    c0
    @4
    c0
    cnvsn0
    unieqi
    uni0
    eqtri
    breq1i
    bitr3i
    syl6bb
end
