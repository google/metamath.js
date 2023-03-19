include "cpr.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wcel.mm"
include "wne.mm"
include "prnzg.mm"
include "syl.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "cfn.mm"
include "hashprlei.mm"
include "simpri.mm"
include "a1i.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "snssd.mm"

theorem upgr1elem
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cS: class S
  let cW: class W
  assume upgr1elem.s: |- ( ph -> { B , C } e. S )
  assume upgr1elem.b: |- ( ph -> B e. W )

  disjoint B x
  disjoint C x
  disjoint S x
  assert |- ( ph -> { { B , C } } C_ { x e. ( S \ { (/) } ) | ( # ` x ) <_ 2 } )

  proof
    wph
    cB
    cC
    cpr
    #
    vx
    cv
    #
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    vx
    cS
    c0
    csn
    cdif
    #
    crab
    #
    wph
    @0
    @4
    wcel
    #
    @0
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    @0
    @5
    wcel
    wph
    @0
    cS
    wcel
    @0
    c0
    wne
    #
    @6
    upgr1elem.s
    wph
    cB
    cW
    wcel
    @9
    upgr1elem.b
    cB
    cC
    cW
    prnzg
    syl
    @0
    cS
    c0
    eldifsn
    sylanbrc
    @8
    wph
    @0
    cfn
    wcel
    @8
    cB
    cC
    hashprlei
    simpri
    a1i
    @3
    @8
    vx
    @0
    @4
    @1
    @0
    wceq
    @2
    @7
    c2
    cle
    @1
    @0
    chash
    fveq2
    breq1d
    elrab
    sylanbrc
    snssd
end
