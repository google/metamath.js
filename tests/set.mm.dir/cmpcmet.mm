include "c1.mm"
include "crp.mm"
include "wcel.mm"
include "1rp.mm"
include "a1i.mm"
include "cv.mm"
include "wa.mm"
include "ccmp.mm"
include "cbl.mm"
include "cfv.mm"
include "co.mm"
include "ccl.mm"
include "ccld.mm"
include "crest.mm"
include "adantr.mm"
include "ctop.mm"
include "cuni.mm"
include "wss.mm"
include "cxmt.mm"
include "cme.mm"
include "metxmet.mm"
include "syl.mm"
include "mopntop.mm"
include "cxr.mm"
include "simpr.mm"
include "rpxr.mm"
include "mp1i.mm"
include "blssm.mm"
include "syl3anc.mm"
include "wceq.mm"
include "mopnuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "clscld.mm"
include "syl2anc.mm"
include "cmpcld.mm"
include "relcmpcmet.mm"

theorem cmpcmet
  let wph: wff ph
  let cD: class D
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  let cR: class R
  assume relcmpcmet.1: |- J = ( MetOpen ` D )
  assume relcmpcmet.2: |- ( ph -> D e. ( Met ` X ) )
  assume cmpcmet.3: |- ( ph -> J e. Comp )


  assert |- ( ph -> D e. ( CMet ` X ) )

  proof
    wph
    vx
    cD
    c1
    cJ
    cX
    relcmpcmet.1
    relcmpcmet.2
    c1
    crp
    wcel
    #
    wph
    1rp
    a1i
    wph
    vx
    cv
    #
    cX
    wcel
    #
    wa
    #
    cJ
    ccmp
    wcel
    #
    @1
    c1
    cD
    cbl
    cfv
    co
    #
    cJ
    ccl
    cfv
    cfv
    #
    cJ
    ccld
    cfv
    wcel
    #
    cJ
    @6
    crest
    co
    ccmp
    wcel
    wph
    @4
    @2
    cmpcmet.3
    adantr
    @3
    cJ
    ctop
    wcel
    #
    @5
    cJ
    cuni
    #
    wss
    @7
    @3
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @8
    wph
    @10
    @2
    wph
    cD
    cX
    cme
    cfv
    wcel
    @10
    relcmpcmet.2
    cD
    cX
    metxmet
    syl
    adantr
    #
    cD
    cJ
    cX
    relcmpcmet.1
    mopntop
    syl
    @3
    @5
    cX
    @9
    @3
    @10
    @2
    c1
    cxr
    wcel
    #
    @5
    cX
    wss
    @11
    wph
    @2
    simpr
    @0
    @12
    @3
    1rp
    c1
    rpxr
    mp1i
    cD
    @1
    c1
    cX
    blssm
    syl3anc
    @3
    @10
    cX
    @9
    wceq
    @11
    cD
    cJ
    cX
    relcmpcmet.1
    mopnuni
    syl
    sseqtrd
    @5
    cJ
    @9
    @9
    eqid
    clscld
    syl2anc
    @6
    cJ
    cmpcld
    syl2anc
    relcmpcmet
end
