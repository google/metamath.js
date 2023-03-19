include "cc0.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cioo.mm"
include "cv.mm"
include "cr.mm"
include "cdv.mm"
include "citg.mm"
include "cicc.mm"
include "wss.mm"
include "ioossicc.mm"
include "a1i.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
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
include "ioossre.mm"
include "eqsstri.mm"
include "sseldi.mm"
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
include "syl3anc.mm"
include "iblss.mm"
include "syldan.mm"
include "itgge0.mm"
include "fss.mm"
include "sylancl.mm"
include "ftc2re.mm"
include "breqtrd.mm"
include "subge0d.mm"
include "mpbid.mm"

theorem fdvposle
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
  assume fdvposle.le: |- ( ph -> A <_ B )
  assume fdvposle.1: |- ( ( ph /\ x e. ( A (,) B ) ) -> 0 <_ ( ( RR _D F ) ` x ) )

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
  assert |- ( ph -> ( F ` A ) <_ ( F ` B ) )

  proof
    wph
    cc0
    cB
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    cmin
    co
    #
    cle
    wbr
    @1
    @0
    cle
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
    cle
    wph
    vx
    @3
    @6
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
    @7
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
    @7
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
    @9
    wph
    @5
    cE
    cr
    ccncf
    co
    #
    wcel
    #
    @10
    fdvposlt.c
    cE
    cr
    @5
    cncff
    syl
    #
    adantr
    wph
    @7
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
    cA
    cr
    wcel
    cB
    cr
    wcel
    vx
    @7
    @6
    cmpt
    #
    @7
    cc
    ccncf
    co
    #
    wcel
    @16
    cibl
    wcel
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
    wph
    cE
    cr
    cB
    @18
    fdvposlt.b
    sseldi
    wph
    @7
    cr
    ccncf
    co
    #
    @17
    @16
    cr
    cc
    wss
    #
    cc
    cc
    wss
    #
    @19
    @17
    wss
    ax-resscn
    cc
    ssid
    #
    @7
    cr
    cc
    cncfss
    mp2an
    wph
    @5
    @7
    cres
    #
    @16
    @19
    wph
    vx
    cE
    cr
    @7
    @5
    @13
    @14
    feqresmpt
    wph
    @7
    cE
    wss
    @12
    @23
    @19
    wcel
    @14
    fdvposlt.c
    cE
    cr
    @7
    @5
    rescncf
    sylc
    eqeltrrd
    sseldi
    cA
    cB
    @16
    cniccibl
    syl3anc
    iblss
    wph
    @4
    @3
    wcel
    #
    wa
    cE
    cr
    @4
    @5
    wph
    @10
    @24
    @13
    adantr
    wph
    @24
    @9
    @4
    cE
    wcel
    wph
    @3
    @7
    @4
    @8
    sselda
    @15
    syldan
    ffvelrnd
    fdvposle.1
    itgge0
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
    fdvposle.le
    wph
    cE
    cr
    cF
    wf
    @20
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
    @11
    cE
    cc
    ccncf
    co
    #
    @5
    @20
    @21
    @11
    @25
    wss
    ax-resscn
    @22
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
    cB
    cF
    fdvposlt.f
    fdvposlt.b
    ffvelrnd
    wph
    cE
    cr
    cA
    cF
    fdvposlt.f
    fdvposlt.a
    ffvelrnd
    subge0d
    mpbid
end
