include "csetrecs.mm"
include "eqid.mm"
include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "wa.mm"
include "csn.mm"
include "cima.mm"
include "cuni.mm"
include "imass1.mm"
include "syl.mm"
include "unissd.mm"
include "wfun.mm"
include "wceq.mm"
include "funss.mm"
include "sylc.mm"
include "funfv.mm"
include "3sstr4d.mm"
include "adantr.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "a1i.mm"
include "simpr.mm"
include "setrec1.mm"
include "sstrd.mm"
include "ex.mm"
include "alrimiv.mm"
include "setrec2v.mm"

theorem setrecsss
  let wph: wff ph
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vk: setvar k
  assume setrecsss.1: |- ( ph -> Fun G )
  assume setrecsss.2: |- ( ph -> F C_ G )


  assert |- ( ph -> setrecs ( F ) C_ setrecs ( G ) )

  proof
    wph
    cF
    csetrecs
    #
    cG
    csetrecs
    #
    cF
    vx
    @0
    eqid
    wph
    vx
    cv
    #
    @1
    wss
    #
    @2
    cF
    cfv
    #
    @1
    wss
    #
    wi
    vx
    wph
    @3
    @5
    wph
    @3
    wa
    #
    @4
    @2
    cG
    cfv
    #
    @1
    wph
    @4
    @7
    wss
    @3
    wph
    cF
    @2
    csn
    #
    cima
    #
    cuni
    #
    cG
    @8
    cima
    #
    cuni
    #
    @4
    @7
    wph
    @9
    @11
    wph
    cF
    cG
    wss
    #
    @9
    @11
    wss
    setrecsss.2
    cF
    cG
    @8
    imass1
    syl
    unissd
    wph
    cF
    wfun
    #
    @4
    @10
    wceq
    wph
    @13
    cG
    wfun
    #
    @14
    setrecsss.2
    setrecsss.1
    cF
    cG
    funss
    sylc
    @2
    cF
    funfv
    syl
    wph
    @15
    @7
    @12
    wceq
    setrecsss.1
    @2
    cG
    funfv
    syl
    3sstr4d
    adantr
    @6
    @2
    @1
    cG
    @1
    eqid
    @2
    cvv
    wcel
    @6
    vx
    vex
    a1i
    wph
    @3
    simpr
    setrec1
    sstrd
    ex
    alrimiv
    setrec2v
end
