include "clidl.mm"
include "cfv.mm"
include "wceq.mm"
include "crsp.mm"
include "crglmod.mm"
include "clss.mm"
include "cbs.mm"
include "rlmbas.mm"
include "syl6eq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "co.mm"
include "rlmplusg.mm"
include "oveqi.mm"
include "3eqtr3g.mm"
include "cvsca.mm"
include "cmulr.mm"
include "rlmvsca.mm"
include "syl5eqelr.mm"
include "csca.mm"
include "cid.mm"
include "cnx.mm"
include "baseid.mm"
include "eqid.mm"
include "strfvi.mm"
include "rlmsca2.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "lsspropd.mm"
include "lidlval.mm"
include "3eqtr4g.mm"
include "clspn.mm"
include "fvexd.mm"
include "lsppropd.mm"
include "rspval.mm"
include "jca.mm"

theorem lidlrsppropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let cW: class W
  assume lidlpropd.1: |- ( ph -> B = ( Base ` K ) )
  assume lidlpropd.2: |- ( ph -> B = ( Base ` L ) )
  assume lidlpropd.3: |- ( ph -> B C_ W )
  assume lidlpropd.4: |- ( ( ph /\ ( x e. W /\ y e. W ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume lidlpropd.5: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` K ) y ) e. W )
  assume lidlpropd.6: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( .r ` K ) y ) = ( x ( .r ` L ) y ) )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint W x
  disjoint W y
  assert |- ( ph -> ( ( LIdeal ` K ) = ( LIdeal ` L ) /\ ( RSpan ` K ) = ( RSpan ` L ) ) )

  proof
    wph
    cK
    clidl
    cfv
    #
    cL
    clidl
    cfv
    #
    wceq
    cK
    crsp
    cfv
    #
    cL
    crsp
    cfv
    #
    wceq
    wph
    cK
    crglmod
    cfv
    #
    clss
    cfv
    cL
    crglmod
    cfv
    #
    clss
    cfv
    @0
    @1
    wph
    vx
    vy
    cB
    cB
    @4
    @5
    cW
    wph
    cB
    cK
    cbs
    cfv
    #
    @4
    cbs
    cfv
    lidlpropd.1
    cK
    rlmbas
    syl6eq
    #
    wph
    cB
    cL
    cbs
    cfv
    #
    @5
    cbs
    cfv
    lidlpropd.2
    cL
    rlmbas
    syl6eq
    #
    lidlpropd.3
    wph
    vx
    cv
    #
    cW
    wcel
    vy
    cv
    #
    cW
    wcel
    wa
    wa
    @10
    @11
    cK
    cplusg
    cfv
    #
    co
    @10
    @11
    cL
    cplusg
    cfv
    #
    co
    @10
    @11
    @4
    cplusg
    cfv
    #
    co
    @10
    @11
    @5
    cplusg
    cfv
    #
    co
    lidlpropd.4
    @12
    @14
    @10
    @11
    cK
    rlmplusg
    oveqi
    @13
    @15
    @10
    @11
    cL
    rlmplusg
    oveqi
    3eqtr3g
    #
    wph
    @10
    cB
    wcel
    @11
    cB
    wcel
    wa
    wa
    #
    @10
    @11
    @4
    cvsca
    cfv
    #
    co
    #
    @10
    @11
    cK
    cmulr
    cfv
    #
    co
    #
    cW
    @20
    @18
    @10
    @11
    cK
    rlmvsca
    oveqi
    #
    lidlpropd.5
    syl5eqelr
    #
    @17
    @21
    @10
    @11
    cL
    cmulr
    cfv
    #
    co
    @19
    @10
    @11
    @5
    cvsca
    cfv
    #
    co
    lidlpropd.6
    @22
    @24
    @25
    @10
    @11
    cL
    rlmvsca
    oveqi
    3eqtr3g
    #
    wph
    cB
    @6
    @4
    csca
    cfv
    #
    cbs
    cfv
    #
    lidlpropd.1
    @6
    cK
    cid
    cfv
    #
    cbs
    cfv
    @28
    cK
    cbs
    cnx
    cbs
    cfv
    #
    @6
    baseid
    @6
    eqid
    strfvi
    @29
    @27
    cbs
    cK
    rlmsca2
    fveq2i
    eqtri
    syl6eq
    #
    wph
    cB
    @8
    @5
    csca
    cfv
    #
    cbs
    cfv
    #
    lidlpropd.2
    @8
    cL
    cid
    cfv
    #
    cbs
    cfv
    @33
    cL
    cbs
    @30
    @8
    baseid
    @8
    eqid
    strfvi
    @34
    @32
    cbs
    cL
    rlmsca2
    fveq2i
    eqtri
    syl6eq
    #
    lsspropd
    cK
    lidlval
    cL
    lidlval
    3eqtr4g
    wph
    @4
    clspn
    cfv
    @5
    clspn
    cfv
    @2
    @3
    wph
    vx
    vy
    cB
    cB
    @4
    @5
    cW
    @7
    @9
    lidlpropd.3
    @16
    @23
    @26
    @31
    @35
    wph
    cK
    crglmod
    fvexd
    wph
    cL
    crglmod
    fvexd
    lsppropd
    cK
    rspval
    cL
    rspval
    3eqtr4g
    jca
end
