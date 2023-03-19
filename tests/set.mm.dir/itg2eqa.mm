include "citg2.mm"
include "cfv.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cr.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "iccssxr.mm"
include "wf.mm"
include "eldifi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "sseldi.mm"
include "xrleid.mm"
include "syl.mm"
include "breqtrd.mm"
include "itg2lea.mm"
include "eqbrtrrd.mm"
include "wb.mm"
include "itg2cl.mm"
include "xrletri3.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem itg2eqa
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let vf: setvar f
  assume itg2lea.1: |- ( ph -> F : RR --> ( 0 [,] +oo ) )
  assume itg2lea.2: |- ( ph -> G : RR --> ( 0 [,] +oo ) )
  assume itg2lea.3: |- ( ph -> A C_ RR )
  assume itg2lea.4: |- ( ph -> ( vol* ` A ) = 0 )
  assume itg2eqa.5: |- ( ( ph /\ x e. ( RR \ A ) ) -> ( F ` x ) = ( G ` x ) )

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint ph x
  disjoint f x
  disjoint F f
  disjoint G f
  disjoint f ph
  assert |- ( ph -> ( S.2 ` F ) = ( S.2 ` G ) )

  proof
    wph
    cF
    citg2
    cfv
    #
    cG
    citg2
    cfv
    #
    wceq
    #
    @0
    @1
    cle
    wbr
    #
    @1
    @0
    cle
    wbr
    #
    wph
    vx
    cA
    cF
    cG
    itg2lea.1
    itg2lea.2
    itg2lea.3
    itg2lea.4
    wph
    vx
    cv
    #
    cr
    cA
    cdif
    wcel
    #
    wa
    #
    @5
    cF
    cfv
    #
    @8
    @5
    cG
    cfv
    #
    cle
    @7
    @8
    cxr
    wcel
    @8
    @8
    cle
    wbr
    @7
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @8
    cc0
    cpnf
    iccssxr
    wph
    cr
    @10
    cF
    wf
    #
    @5
    cr
    wcel
    @8
    @10
    wcel
    @6
    itg2lea.1
    @5
    cr
    cA
    eldifi
    cr
    @10
    @5
    cF
    ffvelrn
    syl2an
    sseldi
    @8
    xrleid
    syl
    #
    itg2eqa.5
    breqtrd
    itg2lea
    wph
    vx
    cA
    cG
    cF
    itg2lea.2
    itg2lea.1
    itg2lea.3
    itg2lea.4
    @7
    @8
    @9
    @8
    cle
    itg2eqa.5
    @12
    eqbrtrrd
    itg2lea
    wph
    @0
    cxr
    wcel
    #
    @1
    cxr
    wcel
    #
    @2
    @3
    @4
    wa
    wb
    wph
    @11
    @13
    itg2lea.1
    cF
    itg2cl
    syl
    wph
    cr
    @10
    cG
    wf
    @14
    itg2lea.2
    cG
    itg2cl
    syl
    @0
    @1
    xrletri3
    syl2anc
    mpbir2and
end
