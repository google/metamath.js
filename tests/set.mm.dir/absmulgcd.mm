include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cabs.mm"
include "cfv.mm"
include "cgcd.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "wa.mm"
include "cn0.mm"
include "gcdcl.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "absidd.mm"
include "syl.mm"
include "oveq2d.mm"
include "3adant1.mm"
include "cc.mm"
include "zcn.mm"
include "nn0cnd.mm"
include "absmul.mm"
include "syl2an.mm"
include "3impb.mm"
include "oveqan12d.mm"
include "3impdi.mm"
include "syl3an.mm"
include "zmulcl.mm"
include "gcdabs.mm"
include "nn0abscl.mm"
include "zabscl.mm"
include "mulgcd.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"

theorem absmulgcd
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( ( K x. M ) gcd ( K x. N ) ) = ( abs ` ( K x. ( M gcd N ) ) ) )

  proof
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cK
    cabs
    cfv
    #
    cM
    cN
    cgcd
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @4
    @5
    cmul
    co
    #
    cK
    @5
    cmul
    co
    cabs
    cfv
    #
    cK
    cM
    cmul
    co
    #
    cK
    cN
    cmul
    co
    #
    cgcd
    co
    #
    @1
    @2
    @7
    @8
    wceq
    @0
    @1
    @2
    wa
    #
    @6
    @5
    @4
    cmul
    @13
    @5
    cn0
    wcel
    #
    @6
    @5
    wceq
    cM
    cN
    gcdcl
    #
    @14
    @5
    @5
    nn0re
    @5
    nn0ge0
    absidd
    syl
    oveq2d
    3adant1
    @0
    @1
    @2
    @9
    @7
    wceq
    #
    @0
    cK
    cc
    wcel
    #
    @5
    cc
    wcel
    @16
    @13
    cK
    zcn
    #
    @13
    @5
    @15
    nn0cnd
    cK
    @5
    absmul
    syl2an
    3impb
    @3
    @12
    @4
    cM
    cabs
    cfv
    #
    cN
    cabs
    cfv
    #
    cgcd
    co
    #
    cmul
    co
    #
    @8
    @3
    @10
    cabs
    cfv
    #
    @11
    cabs
    cfv
    #
    cgcd
    co
    #
    @4
    @19
    cmul
    co
    #
    @4
    @20
    cmul
    co
    #
    cgcd
    co
    #
    @12
    @22
    @0
    @17
    @1
    cM
    cc
    wcel
    #
    @2
    cN
    cc
    wcel
    #
    @25
    @28
    wceq
    #
    @18
    cM
    zcn
    cN
    zcn
    @17
    @29
    @30
    @31
    @17
    @29
    wa
    @17
    @30
    wa
    @23
    @26
    @24
    @27
    cgcd
    cK
    cM
    absmul
    cK
    cN
    absmul
    oveqan12d
    3impdi
    syl3an
    @0
    @1
    @2
    @25
    @12
    wceq
    #
    @0
    @1
    wa
    @10
    cz
    wcel
    @11
    cz
    wcel
    @32
    @0
    @2
    wa
    cK
    cM
    zmulcl
    cK
    cN
    zmulcl
    @10
    @11
    gcdabs
    syl2an
    3impdi
    @0
    @4
    cn0
    wcel
    @1
    @19
    cz
    wcel
    @2
    @20
    cz
    wcel
    @28
    @22
    wceq
    cK
    nn0abscl
    cM
    zabscl
    cN
    zabscl
    @4
    @19
    @20
    mulgcd
    syl3an
    3eqtr3d
    @3
    @21
    @5
    @4
    cmul
    @1
    @2
    @21
    @5
    wceq
    @0
    cM
    cN
    gcdabs
    3adant1
    oveq2d
    eqtrd
    3eqtr4rd
end
