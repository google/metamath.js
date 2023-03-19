include "ctsu.mm"
include "co.mm"
include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "ctop.mm"
include "ctopon.mm"
include "ctgp.mm"
include "tgptopon.mm"
include "syl.mm"
include "topontop.mm"
include "0cld.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "wne.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "wa.mm"
include "csn.mm"
include "ccl.mm"
include "ccmn.mm"
include "adantr.mm"
include "wf.mm"
include "simpr.mm"
include "tgptsmscls.mm"
include "cuni.mm"
include "wss.mm"
include "ctps.mm"
include "tgptps.mm"
include "tsmscl.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "sselda.mm"
include "snssd.mm"
include "eqid.mm"
include "clscld.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "pm2.61dne.mm"

theorem tgptsmscld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cJ: class J
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  let cX: class X
  assume tgptsmscls.b: |- B = ( Base ` G )
  assume tgptsmscls.j: |- J = ( TopOpen ` G )
  assume tgptsmscls.1: |- ( ph -> G e. CMnd )
  assume tgptsmscls.2: |- ( ph -> G e. TopGrp )
  assume tgptsmscls.a: |- ( ph -> A e. V )
  assume tgptsmscls.f: |- ( ph -> F : A --> B )


  assert |- ( ph -> ( G tsums F ) e. ( Clsd ` J ) )

  proof
    wph
    cG
    cF
    ctsu
    co
    #
    cJ
    ccld
    cfv
    #
    wcel
    #
    @0
    c0
    wph
    @2
    @0
    c0
    wceq
    c0
    @1
    wcel
    #
    wph
    cJ
    ctop
    wcel
    #
    @3
    wph
    cJ
    cB
    ctopon
    cfv
    wcel
    #
    @4
    wph
    cG
    ctgp
    wcel
    #
    @5
    tgptsmscls.2
    cG
    cJ
    cB
    tgptsmscls.j
    tgptsmscls.b
    tgptopon
    syl
    #
    cB
    cJ
    topontop
    syl
    #
    cJ
    0cld
    syl
    @0
    c0
    @1
    eleq1
    syl5ibrcom
    @0
    c0
    wne
    vx
    cv
    #
    @0
    wcel
    #
    vx
    wex
    wph
    @2
    vx
    @0
    n0
    wph
    @10
    @2
    vx
    wph
    @10
    @2
    wph
    @10
    wa
    #
    @0
    @9
    csn
    #
    cJ
    ccl
    cfv
    cfv
    #
    @1
    @11
    cA
    cB
    cF
    cG
    cJ
    cV
    @9
    tgptsmscls.b
    tgptsmscls.j
    wph
    cG
    ccmn
    wcel
    @10
    tgptsmscls.1
    adantr
    wph
    @6
    @10
    tgptsmscls.2
    adantr
    wph
    cA
    cV
    wcel
    @10
    tgptsmscls.a
    adantr
    wph
    cA
    cB
    cF
    wf
    @10
    tgptsmscls.f
    adantr
    wph
    @10
    simpr
    tgptsmscls
    @11
    @4
    @12
    cJ
    cuni
    #
    wss
    @13
    @1
    wcel
    wph
    @4
    @10
    @8
    adantr
    @11
    @9
    @14
    wph
    @0
    @14
    @9
    wph
    @0
    cB
    @14
    wph
    cA
    cB
    cF
    cG
    cV
    tgptsmscls.b
    tgptsmscls.1
    wph
    @6
    cG
    ctps
    wcel
    tgptsmscls.2
    cG
    tgptps
    syl
    tgptsmscls.a
    tgptsmscls.f
    tsmscl
    wph
    @5
    cB
    @14
    wceq
    @7
    cB
    cJ
    toponuni
    syl
    sseqtrd
    sselda
    snssd
    @12
    cJ
    @14
    @14
    eqid
    clscld
    syl2anc
    eqeltrd
    ex
    exlimdv
    syl5bi
    pm2.61dne
end
