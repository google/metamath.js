include "c1.mm"
include "cr.mm"
include "ccpn.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "cdvn.mm"
include "cdm.mm"
include "ccncf.mm"
include "wss.mm"
include "cn0.mm"
include "wa.mm"
include "wb.mm"
include "ax-resscn.mm"
include "1nn0.mm"
include "elcpn.mm"
include "mp2an.mm"
include "simplbi.mm"
include "syl.mm"
include "cicc.mm"
include "cdv.mm"
include "cres.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wfun.mm"
include "pmfun.mm"
include "funfn.mm"
include "sylib.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "cnex.mm"
include "reex.mm"
include "elpm2.mm"
include "simprbi.mm"
include "dvfre.mm"
include "syl2anc.mm"
include "wceq.mm"
include "cc0.mm"
include "caddc.mm"
include "0p1e1.mm"
include "fveq2i.mm"
include "0nn0.mm"
include "dvnp1.mm"
include "mp3an13.mm"
include "syl5eqr.mm"
include "dvn0.mm"
include "sylancr.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "eqeltrrd.mm"
include "cncff.mm"
include "fdm.mm"
include "3syl.mm"
include "feq2d.mm"
include "mpbid.mm"
include "cncffvrn.mm"
include "mpbird.mm"
include "rescncf.mm"
include "sylc.mm"
include "cpr.mm"
include "cuz.mm"
include "prid1.mm"
include "1eluzge0.mm"
include "cpnord.mm"
include "mp3an.mm"
include "sseldi.mm"
include "c1lip1.mm"

theorem c1lip2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  assume c1lip2.a: |- ( ph -> A e. RR )
  assume c1lip2.b: |- ( ph -> B e. RR )
  assume c1lip2.f: |- ( ph -> F e. ( ( C^n ` RR ) ` 1 ) )
  assume c1lip2.rn: |- ( ph -> ran F C_ RR )
  assume c1lip2.dm: |- ( ph -> ( A [,] B ) C_ dom F )

  disjoint ph x
  disjoint ph y
  disjoint k ph
  disjoint x y
  disjoint k x
  disjoint k y
  disjoint A x
  disjoint A y
  disjoint A k
  disjoint B x
  disjoint B y
  disjoint B k
  disjoint F x
  disjoint F y
  disjoint F k
  assert |- ( ph -> E. k e. RR A. x e. ( A [,] B ) A. y e. ( A [,] B ) ( abs ` ( ( F ` y ) - ( F ` x ) ) ) <_ ( k x. ( abs ` ( y - x ) ) ) )

  proof
    wph
    vx
    vy
    cA
    cB
    vk
    cF
    c1lip2.a
    c1lip2.b
    wph
    cF
    c1
    cr
    ccpn
    cfv
    #
    cfv
    #
    wcel
    #
    cF
    cc
    cr
    cpm
    co
    wcel
    #
    c1lip2.f
    @2
    @3
    c1
    cr
    cF
    cdvn
    co
    #
    cfv
    #
    cF
    cdm
    #
    cc
    ccncf
    co
    #
    wcel
    #
    cr
    cc
    wss
    #
    c1
    cn0
    wcel
    @2
    @3
    @8
    wa
    wb
    ax-resscn
    1nn0
    cr
    cF
    c1
    elcpn
    mp2an
    #
    simplbi
    syl
    #
    wph
    cA
    cB
    cicc
    co
    #
    @6
    wss
    #
    cr
    cF
    cdv
    co
    #
    @6
    cr
    ccncf
    co
    #
    wcel
    #
    @14
    @12
    cres
    @12
    cr
    ccncf
    co
    #
    wcel
    c1lip2.dm
    wph
    @16
    @6
    cr
    @14
    wf
    #
    wph
    @14
    cdm
    #
    cr
    @14
    wf
    #
    @18
    wph
    @6
    cr
    cF
    wf
    #
    @6
    cr
    wss
    #
    @20
    wph
    cF
    @6
    wfn
    #
    cF
    crn
    cr
    wss
    @21
    wph
    cF
    wfun
    #
    @23
    wph
    @3
    @24
    @11
    cc
    cr
    cF
    pmfun
    syl
    cF
    funfn
    sylib
    c1lip2.rn
    @6
    cr
    cF
    df-f
    sylanbrc
    #
    wph
    @3
    @22
    @11
    @3
    @6
    cc
    cF
    wf
    @22
    cc
    cr
    cF
    cnex
    reex
    elpm2
    simprbi
    syl
    @6
    cF
    dvfre
    syl2anc
    wph
    @19
    @6
    cr
    @14
    wph
    @14
    @7
    wcel
    #
    @6
    cc
    @14
    wf
    @19
    @6
    wceq
    wph
    @5
    @14
    @7
    wph
    @5
    cr
    cc0
    @4
    cfv
    #
    cdv
    co
    #
    @14
    wph
    @5
    cc0
    c1
    caddc
    co
    #
    @4
    cfv
    #
    @28
    @29
    c1
    @4
    0p1e1
    fveq2i
    wph
    @3
    @30
    @28
    wceq
    #
    @11
    @9
    @3
    cc0
    cn0
    wcel
    #
    @31
    ax-resscn
    0nn0
    cr
    cF
    cc0
    dvnp1
    mp3an13
    syl
    syl5eqr
    wph
    @27
    cF
    cr
    cdv
    wph
    @9
    @3
    @27
    cF
    wceq
    ax-resscn
    @11
    cr
    cF
    dvn0
    sylancr
    #
    oveq2d
    eqtrd
    wph
    @2
    @8
    c1lip2.f
    @2
    @3
    @8
    @10
    simprbi
    syl
    eqeltrrd
    #
    @6
    cc
    @14
    cncff
    @6
    cc
    @14
    fdm
    3syl
    feq2d
    mpbid
    wph
    @9
    @26
    @16
    @18
    wb
    ax-resscn
    @34
    @6
    cc
    cr
    @14
    cncffvrn
    sylancr
    mpbird
    @6
    cr
    @12
    @14
    rescncf
    sylc
    wph
    @13
    cF
    @15
    wcel
    #
    cF
    @12
    cres
    @17
    wcel
    c1lip2.dm
    wph
    @35
    @21
    @25
    wph
    @9
    cF
    @7
    wcel
    @35
    @21
    wb
    ax-resscn
    wph
    @27
    cF
    @7
    @33
    wph
    cF
    cc0
    @0
    cfv
    #
    wcel
    #
    @27
    @7
    wcel
    #
    wph
    @1
    @36
    cF
    cr
    cr
    cc
    cpr
    wcel
    @32
    c1
    cc0
    cuz
    cfv
    wcel
    @1
    @36
    wss
    cr
    cc
    reex
    prid1
    0nn0
    1eluzge0
    cr
    cc0
    c1
    cpnord
    mp3an
    c1lip2.f
    sseldi
    @37
    @3
    @38
    @9
    @32
    @37
    @3
    @38
    wa
    wb
    ax-resscn
    0nn0
    cr
    cF
    cc0
    elcpn
    mp2an
    simprbi
    syl
    eqeltrrd
    @6
    cc
    cr
    cF
    cncffvrn
    sylancr
    mpbird
    @6
    cr
    @12
    cF
    rescncf
    sylc
    c1lip1
end
