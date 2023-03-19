include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "co.mm"
include "wral.mm"
include "wrex.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "crest.mm"
include "cuni.mm"
include "eqid.mm"
include "cr.mm"
include "wcel.mm"
include "ccmp.mm"
include "icccmp.mm"
include "syl2anc.mm"
include "ccncf.mm"
include "ccn.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "cc.mm"
include "wss.mm"
include "wceq.mm"
include "iccssre.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "tgioo.mm"
include "cncfmet.mm"
include "sylancl.mm"
include "resubmet.mm"
include "syl.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "eleqtrd.mm"
include "c0.mm"
include "ctop.mm"
include "retop.mm"
include "uniretop.mm"
include "restuni.mm"
include "sylancr.mm"
include "wne.mm"
include "cxr.mm"
include "rexrd.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "ne0i.mm"
include "eqnetrrd.mm"
include "evth.mm"
include "raleqdv.mm"
include "rexeqbidv.mm"
include "mpbird.mm"
include "evth2.mm"
include "jca.mm"

theorem evthicc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cF: class F
  let va: setvar a
  let vb: setvar b
  assume evthicc.1: |- ( ph -> A e. RR )
  assume evthicc.2: |- ( ph -> B e. RR )
  assume evthicc.3: |- ( ph -> A <_ B )
  assume evthicc.4: |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B w
  disjoint B z
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint ph w
  disjoint ph z
  disjoint F w
  disjoint F z
  disjoint a b
  disjoint a w
  disjoint a z
  disjoint A a
  disjoint b w
  disjoint b z
  disjoint A b
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint F a
  disjoint F b
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> ( E. x e. ( A [,] B ) A. y e. ( A [,] B ) ( F ` y ) <_ ( F ` x ) /\ E. z e. ( A [,] B ) A. w e. ( A [,] B ) ( F ` z ) <_ ( F ` w ) ) )

  proof
    wph
    vy
    cv
    cF
    cfv
    vx
    cv
    cF
    cfv
    cle
    wbr
    #
    vy
    cA
    cB
    cicc
    co
    #
    wral
    #
    vx
    @1
    wrex
    #
    vz
    cv
    cF
    cfv
    vw
    cv
    cF
    cfv
    cle
    wbr
    #
    vw
    @1
    wral
    #
    vz
    @1
    wrex
    #
    wph
    @3
    @0
    vy
    cioo
    crn
    ctg
    cfv
    #
    @1
    crest
    co
    #
    cuni
    #
    wral
    #
    vx
    @9
    wrex
    wph
    vx
    vy
    cF
    @8
    @7
    @9
    @9
    eqid
    #
    @7
    eqid
    #
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @8
    ccmp
    wcel
    evthicc.1
    evthicc.2
    cA
    cB
    @8
    @7
    @12
    @8
    eqid
    icccmp
    syl2anc
    #
    wph
    cF
    @1
    cr
    ccncf
    co
    #
    @8
    @7
    ccn
    co
    #
    evthicc.4
    wph
    @16
    cabs
    cmin
    ccom
    #
    @1
    @1
    cxp
    cres
    #
    cmopn
    cfv
    #
    @7
    ccn
    co
    #
    @17
    wph
    @1
    cc
    wss
    cr
    cc
    wss
    @16
    @21
    wceq
    wph
    @1
    cr
    cc
    wph
    @13
    @14
    @1
    cr
    wss
    #
    evthicc.1
    evthicc.2
    cA
    cB
    iccssre
    syl2anc
    #
    ax-resscn
    syl6ss
    ax-resscn
    @1
    cr
    @19
    @18
    cr
    cr
    cxp
    cres
    #
    @20
    @7
    @19
    eqid
    @24
    eqid
    #
    @20
    eqid
    #
    @24
    @24
    cmopn
    cfv
    #
    @25
    @27
    eqid
    tgioo
    cncfmet
    sylancl
    wph
    @20
    @8
    @7
    ccn
    wph
    @22
    @20
    @8
    wceq
    @23
    @1
    @7
    @20
    @12
    @26
    resubmet
    syl
    oveq1d
    eqtrd
    eleqtrd
    #
    wph
    @1
    @9
    c0
    wph
    @7
    ctop
    wcel
    @22
    @1
    @9
    wceq
    retop
    @23
    @1
    @7
    cr
    uniretop
    restuni
    sylancr
    #
    wph
    cA
    @1
    wcel
    #
    @1
    c0
    wne
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    cle
    wbr
    @30
    wph
    cA
    evthicc.1
    rexrd
    wph
    cB
    evthicc.2
    rexrd
    evthicc.3
    cA
    cB
    lbicc2
    syl3anc
    @1
    cA
    ne0i
    syl
    eqnetrrd
    #
    evth
    wph
    @2
    @10
    vx
    @1
    @9
    @29
    wph
    @0
    vy
    @1
    @9
    @29
    raleqdv
    rexeqbidv
    mpbird
    wph
    @6
    @4
    vw
    @9
    wral
    #
    vz
    @9
    wrex
    wph
    vz
    vw
    cF
    @8
    @7
    @9
    @11
    @12
    @15
    @28
    @31
    evth2
    wph
    @5
    @32
    vz
    @1
    @9
    @29
    wph
    @4
    vw
    @1
    @9
    @29
    raleqdv
    rexeqbidv
    mpbird
    jca
end
