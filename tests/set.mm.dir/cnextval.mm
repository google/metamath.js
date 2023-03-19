include "ctop.mm"
include "cv.mm"
include "cuni.mm"
include "cpm.mm"
include "co.mm"
include "cdm.mm"
include "ccl.mm"
include "cfv.mm"
include "csn.mm"
include "cnei.mm"
include "crest.mm"
include "cflf.mm"
include "cxp.mm"
include "ciun.mm"
include "cmpt.mm"
include "ccnext.mm"
include "wceq.mm"
include "unieq.mm"
include "oveq2d.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "xpeq2d.mm"
include "iuneq12d.mm"
include "mpteq12dv.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "df-cnext.mm"
include "ovex.mm"
include "mptex.mm"
include "ovmpt2.mm"

theorem cnextval
  let vx: setvar x
  let vf: setvar f
  let cJ: class J
  let cK: class K
  let vj: setvar j
  let vk: setvar k

  disjoint f x
  disjoint J f
  disjoint J x
  disjoint K f
  disjoint K x
  disjoint f j
  disjoint f k
  disjoint j k
  disjoint j x
  disjoint J j
  disjoint k x
  disjoint J k
  disjoint K j
  disjoint K k
  assert |- ( ( J e. Top /\ K e. Top ) -> ( J CnExt K ) = ( f e. ( U. K ^pm U. J ) |-> U_ x e. ( ( cls ` J ) ` dom f ) ( { x } X. ( ( K fLimf ( ( ( nei ` J ) ` { x } ) |`t dom f ) ) ` f ) ) ) )

  proof
    vj
    vk
    cJ
    cK
    ctop
    ctop
    vf
    vk
    cv
    #
    cuni
    #
    vj
    cv
    #
    cuni
    #
    cpm
    co
    #
    vx
    vf
    cv
    #
    cdm
    #
    @2
    ccl
    cfv
    #
    cfv
    #
    vx
    cv
    csn
    #
    @5
    @0
    @9
    @2
    cnei
    cfv
    #
    cfv
    #
    @6
    crest
    co
    #
    cflf
    co
    #
    cfv
    #
    cxp
    #
    ciun
    #
    cmpt
    vf
    cK
    cuni
    #
    cJ
    cuni
    #
    cpm
    co
    #
    vx
    @6
    cJ
    ccl
    cfv
    #
    cfv
    #
    @9
    @5
    cK
    @9
    cJ
    cnei
    cfv
    #
    cfv
    #
    @6
    crest
    co
    #
    cflf
    co
    #
    cfv
    #
    cxp
    #
    ciun
    #
    cmpt
    ccnext
    vf
    @1
    @18
    cpm
    co
    #
    vx
    @21
    @9
    @5
    @0
    @24
    cflf
    co
    #
    cfv
    #
    cxp
    #
    ciun
    #
    cmpt
    @2
    cJ
    wceq
    #
    vf
    @4
    @16
    @29
    @33
    @34
    @3
    @18
    @1
    cpm
    @2
    cJ
    unieq
    oveq2d
    @34
    vx
    @8
    @21
    @15
    @32
    @34
    @6
    @7
    @20
    @2
    cJ
    ccl
    fveq2
    fveq1d
    @34
    @14
    @31
    @9
    @34
    @5
    @13
    @30
    @34
    @12
    @24
    @0
    cflf
    @34
    @11
    @23
    @6
    crest
    @34
    @9
    @10
    @22
    @2
    cJ
    cnei
    fveq2
    fveq1d
    oveq1d
    oveq2d
    fveq1d
    xpeq2d
    iuneq12d
    mpteq12dv
    @0
    cK
    wceq
    #
    vf
    @29
    @33
    @19
    @28
    @35
    @1
    @17
    @18
    cpm
    @0
    cK
    unieq
    oveq1d
    @35
    vx
    @21
    @32
    @27
    @35
    @31
    @26
    @9
    @35
    @5
    @30
    @25
    @0
    cK
    @24
    cflf
    oveq1
    fveq1d
    xpeq2d
    iuneq2d
    mpteq12dv
    vx
    vf
    vj
    vk
    df-cnext
    vf
    @19
    @28
    @17
    @18
    cpm
    ovex
    mptex
    ovmpt2
end
