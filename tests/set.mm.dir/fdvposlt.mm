include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cioo.mm"
include "cv.mm"
include "cr.mm"
include "cdv.mm"
include "citg.mm"
include "cvol.mm"
include "ioossre.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "posdifd.mm"
include "mpbid.mm"
include "wcel.mm"
include "cle.mm"
include "wceq.mm"
include "ltled.mm"
include "volioo.mm"
include "syl3anc.mm"
include "breqtrrd.mm"
include "cicc.mm"
include "wss.mm"
include "ioossicc.mm"
include "a1i.mm"
include "cdm.mm"
include "ioombl.mm"
include "wa.mm"
include "wf.mm"
include "ccncf.mm"
include "cncff.mm"
include "syl.mm"
include "adantr.mm"
include "fct2relem.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "cmpt.mm"
include "cc.mm"
include "cibl.mm"
include "ax-resscn.mm"
include "ssid.mm"
include "cncfss.mm"
include "mp2an.mm"
include "cres.mm"
include "feqresmpt.mm"
include "rescncf.mm"
include "sylc.mm"
include "eqeltrrd.mm"
include "cniccibl.mm"
include "iblss.mm"
include "crp.mm"
include "syldan.mm"
include "elrp.mm"
include "sylanbrc.mm"
include "itggt0.mm"
include "fss.mm"
include "sylancl.mm"
include "ftc2re.mm"
include "breqtrd.mm"
include "mpbird.mm"

theorem fdvposlt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let vy: setvar y
  assume fdvposlt.d: |- E = ( C (,) D )
  assume fdvposlt.a: |- ( ph -> A e. E )
  assume fdvposlt.b: |- ( ph -> B e. E )
  assume fdvposlt.f: |- ( ph -> F : E --> RR )
  assume fdvposlt.c: |- ( ph -> ( RR _D F ) e. ( E -cn-> RR ) )
  assume fdvposlt.lt: |- ( ph -> A < B )
  assume fdvposlt.1: |- ( ( ph /\ x e. ( A (,) B ) ) -> 0 < ( ( RR _D F ) ` x ) )

  disjoint A x
  disjoint B x
  disjoint E x
  disjoint F x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint E y
  disjoint F y
  disjoint ph y
  assert |- ( ph -> ( F ` A ) < ( F ` B ) )

  proof
    wph
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    clt
    wbr
    cc0
    @1
    @0
    cmin
    co
    #
    clt
    wbr
    wph
    cc0
    vx
    cA
    cB
    cioo
    co
    #
    vx
    cv
    #
    cr
    cF
    cdv
    co
    #
    cfv
    #
    citg
    @2
    clt
    wph
    vx
    @3
    @6
    wph
    cc0
    cB
    cA
    cmin
    co
    #
    @3
    cvol
    cfv
    #
    clt
    wph
    cA
    cB
    clt
    wbr
    cc0
    @7
    clt
    wbr
    fdvposlt.lt
    wph
    cA
    cB
    wph
    cE
    cr
    cA
    cE
    cC
    cD
    cioo
    co
    cr
    fdvposlt.d
    cC
    cD
    ioossre
    eqsstri
    #
    fdvposlt.a
    sseldi
    #
    wph
    cE
    cr
    cB
    @9
    fdvposlt.b
    sseldi
    #
    posdifd
    mpbid
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    @8
    @7
    wceq
    @10
    @11
    wph
    cA
    cB
    @10
    @11
    fdvposlt.lt
    ltled
    #
    cA
    cB
    volioo
    syl3anc
    breqtrrd
    wph
    vx
    @3
    cA
    cB
    cicc
    co
    #
    @6
    cr
    @3
    @15
    wss
    wph
    cA
    cB
    ioossicc
    a1i
    #
    @3
    cvol
    cdm
    wcel
    wph
    cA
    cB
    ioombl
    a1i
    wph
    @4
    @15
    wcel
    #
    wa
    cE
    cr
    @4
    @5
    wph
    cE
    cr
    @5
    wf
    #
    @17
    wph
    @5
    cE
    cr
    ccncf
    co
    #
    wcel
    #
    @18
    fdvposlt.c
    cE
    cr
    @5
    cncff
    syl
    #
    adantr
    wph
    @15
    cE
    @4
    wph
    cA
    cB
    cC
    cD
    cE
    fdvposlt.d
    fdvposlt.a
    fdvposlt.b
    fct2relem
    #
    sselda
    #
    ffvelrnd
    wph
    @12
    @13
    vx
    @15
    @6
    cmpt
    #
    @15
    cc
    ccncf
    co
    #
    wcel
    @24
    cibl
    wcel
    @10
    @11
    wph
    @15
    cr
    ccncf
    co
    #
    @25
    @24
    cr
    cc
    wss
    #
    cc
    cc
    wss
    #
    @26
    @25
    wss
    ax-resscn
    cc
    ssid
    #
    @15
    cr
    cc
    cncfss
    mp2an
    wph
    @5
    @15
    cres
    #
    @24
    @26
    wph
    vx
    cE
    cr
    @15
    @5
    @21
    @22
    feqresmpt
    wph
    @15
    cE
    wss
    @20
    @30
    @26
    wcel
    @22
    fdvposlt.c
    cE
    cr
    @15
    @5
    rescncf
    sylc
    eqeltrrd
    sseldi
    cA
    cB
    @24
    cniccibl
    syl3anc
    iblss
    wph
    @4
    @3
    wcel
    #
    wa
    #
    @6
    cr
    wcel
    cc0
    @6
    clt
    wbr
    @6
    crp
    wcel
    @32
    cE
    cr
    @4
    @5
    wph
    @18
    @31
    @21
    adantr
    wph
    @31
    @17
    @4
    cE
    wcel
    wph
    @3
    @15
    @4
    @16
    sselda
    @23
    syldan
    ffvelrnd
    fdvposlt.1
    @6
    elrp
    sylanbrc
    itggt0
    wph
    vx
    cA
    cB
    cC
    cD
    cE
    cF
    fdvposlt.d
    fdvposlt.a
    fdvposlt.b
    @14
    wph
    cE
    cr
    cF
    wf
    @27
    cE
    cc
    cF
    wf
    fdvposlt.f
    ax-resscn
    cE
    cr
    cc
    cF
    fss
    sylancl
    wph
    @19
    cE
    cc
    ccncf
    co
    #
    @5
    @27
    @28
    @19
    @33
    wss
    ax-resscn
    @29
    cE
    cr
    cc
    cncfss
    mp2an
    fdvposlt.c
    sseldi
    ftc2re
    breqtrd
    wph
    @0
    @1
    wph
    cE
    cr
    cA
    cF
    fdvposlt.f
    fdvposlt.a
    ffvelrnd
    wph
    cE
    cr
    cB
    cF
    fdvposlt.f
    fdvposlt.b
    ffvelrnd
    posdifd
    mpbird
end
