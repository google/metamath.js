include "crn.mm"
include "cres.mm"
include "csumge0.mm"
include "cfv.mm"
include "ccom.mm"
include "cle.mm"
include "cv.mm"
include "cmpt.mm"
include "cpw.mm"
include "nfv.mm"
include "fveq2.mm"
include "wcel.mm"
include "wceq.mm"
include "fvres.mm"
include "adantl.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "adantr.mm"
include "wss.mm"
include "frn.mm"
include "syl.mm"
include "simpr.mm"
include "sseldd.mm"
include "ffvelrnd.mm"
include "sge0f1o.mm"
include "feqresmpt.mm"
include "fveq2d.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "reseq1d.mm"
include "elpwid.mm"
include "resmptd.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "fco.mm"
include "sge0less.mm"
include "eqbrtrd.mm"

theorem sge0resrnlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume sge0resrnlem.a: |- ( ph -> A e. V )
  assume sge0resrnlem.f: |- ( ph -> F : B --> ( 0 [,] +oo ) )
  assume sge0resrnlem.g: |- ( ph -> G : A --> B )
  assume sge0resrnlem.x: |- ( ph -> X e. ~P A )
  assume sge0resrnlem.f1o: |- ( ph -> ( G |` X ) : X -1-1-onto-> ran G )


  assert |- ( ph -> ( sum^ ` ( F |` ran G ) ) <_ ( sum^ ` ( F o. G ) ) )

  proof
    wph
    cF
    cG
    crn
    #
    cres
    #
    csumge0
    cfv
    #
    cF
    cG
    ccom
    #
    cX
    cres
    #
    csumge0
    cfv
    #
    @3
    csumge0
    cfv
    cle
    wph
    vy
    @0
    vy
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    vx
    cX
    vx
    cv
    #
    cG
    cfv
    #
    cF
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    @2
    @5
    wph
    @0
    @7
    cX
    @11
    vy
    vx
    cG
    cX
    cres
    #
    @10
    cA
    cpw
    wph
    vy
    nfv
    wph
    vx
    nfv
    @6
    @10
    cF
    fveq2
    sge0resrnlem.x
    sge0resrnlem.f1o
    @9
    cX
    wcel
    @9
    @13
    cfv
    @10
    wceq
    wph
    @9
    cX
    cG
    fvres
    adantl
    wph
    @6
    @0
    wcel
    #
    wa
    #
    cB
    cc0
    cpnf
    cicc
    co
    #
    @6
    cF
    wph
    cB
    @16
    cF
    wf
    #
    @14
    sge0resrnlem.f
    adantr
    @15
    @0
    cB
    @6
    wph
    @0
    cB
    wss
    #
    @14
    wph
    cA
    cB
    cG
    wf
    #
    @18
    sge0resrnlem.g
    cA
    cB
    cG
    frn
    syl
    #
    adantr
    wph
    @14
    simpr
    sseldd
    ffvelrnd
    sge0f1o
    wph
    @1
    @8
    csumge0
    wph
    vy
    cB
    @16
    @0
    cF
    sge0resrnlem.f
    @20
    feqresmpt
    fveq2d
    wph
    @4
    @12
    csumge0
    wph
    @4
    vx
    cA
    @11
    cmpt
    #
    cX
    cres
    @12
    wph
    @3
    @21
    cX
    wph
    @17
    @19
    @3
    @21
    wceq
    sge0resrnlem.f
    sge0resrnlem.g
    vx
    cF
    cG
    cA
    cB
    @16
    fcompt
    syl2anc
    reseq1d
    wph
    vx
    cA
    cX
    @11
    wph
    cX
    cA
    sge0resrnlem.x
    elpwid
    resmptd
    eqtrd
    fveq2d
    3eqtr4d
    wph
    @3
    cV
    cA
    cX
    sge0resrnlem.a
    wph
    @17
    @19
    cA
    @16
    @3
    wf
    sge0resrnlem.f
    sge0resrnlem.g
    cA
    cB
    @16
    cF
    cG
    fco
    syl2anc
    sge0less
    eqbrtrd
end
