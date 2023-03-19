include "wss.mm"
include "cv.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cdiv.mm"
include "simpr.mm"
include "rpdivcl.mm"
include "syl2anr.mm"
include "metss2lem.mm"
include "wceq.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ralrimivva.mm"
include "cxmt.mm"
include "wb.mm"
include "cme.mm"
include "metxmet.mm"
include "syl.mm"
include "metss.mm"
include "mpbird.mm"

theorem metss2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cR: class R
  let cJ: class J
  let cK: class K
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  let cS: class S
  let va: setvar a
  let vb: setvar b
  assume metequiv.3: |- J = ( MetOpen ` C )
  assume metequiv.4: |- K = ( MetOpen ` D )
  assume metss2.1: |- ( ph -> C e. ( Met ` X ) )
  assume metss2.2: |- ( ph -> D e. ( Met ` X ) )
  assume metss2.3: |- ( ph -> R e. RR+ )
  assume metss2.4: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( x C y ) <_ ( R x. ( x D y ) ) )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint R y
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint C r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint x z
  disjoint y z
  disjoint C z
  disjoint J r
  disjoint J s
  disjoint K r
  disjoint K s
  disjoint R s
  disjoint S y
  disjoint D r
  disjoint D s
  disjoint D z
  disjoint ph r
  disjoint X r
  disjoint X s
  disjoint X z
  disjoint a b
  disjoint a x
  disjoint C a
  disjoint b x
  disjoint C b
  disjoint D a
  disjoint D b
  disjoint J a
  disjoint J b
  disjoint K a
  disjoint K b
  disjoint X a
  disjoint X b
  assert |- ( ph -> J C_ K )

  proof
    wph
    cJ
    cK
    wss
    #
    vx
    cv
    #
    vs
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    @1
    vr
    cv
    #
    cC
    cbl
    cfv
    co
    #
    wss
    #
    vs
    crp
    wrex
    #
    vr
    crp
    wral
    vx
    cX
    wral
    #
    wph
    @8
    vx
    vr
    cX
    crp
    wph
    @1
    cX
    wcel
    #
    @5
    crp
    wcel
    #
    wa
    #
    wa
    @5
    cR
    cdiv
    co
    #
    crp
    wcel
    #
    @1
    @13
    @3
    co
    #
    @6
    wss
    #
    @8
    @12
    @11
    cR
    crp
    wcel
    @14
    wph
    @10
    @11
    simpr
    metss2.3
    @5
    cR
    rpdivcl
    syl2anr
    wph
    vx
    vy
    cC
    cD
    cR
    @5
    cJ
    cK
    cX
    metequiv.3
    metequiv.4
    metss2.1
    metss2.2
    metss2.3
    metss2.4
    metss2lem
    @7
    @16
    vs
    @13
    crp
    @2
    @13
    wceq
    @4
    @15
    @6
    @2
    @13
    @1
    @3
    oveq2
    sseq1d
    rspcev
    syl2anc
    ralrimivva
    wph
    cC
    cX
    cxmt
    cfv
    #
    wcel
    #
    cD
    @17
    wcel
    #
    @0
    @9
    wb
    wph
    cC
    cX
    cme
    cfv
    #
    wcel
    @18
    metss2.1
    cC
    cX
    metxmet
    syl
    wph
    cD
    @20
    wcel
    @19
    metss2.2
    cD
    cX
    metxmet
    syl
    vx
    cC
    cD
    cJ
    cK
    cX
    vs
    vr
    metequiv.3
    metequiv.4
    metss
    syl2anc
    mpbird
end
