include "c1.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "cc.mm"
include "crab.mm"
include "cn0.mm"
include "cexp.mm"
include "csu.mm"
include "cmpt.mm"
include "cc0.mm"
include "cicc.mm"
include "cres.mm"
include "ccncf.mm"
include "wss.mm"
include "cr.mm"
include "unitssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "1re.mm"
include "w3a.mm"
include "simpr.mm"
include "0re.mm"
include "elicc2i.mm"
include "sylib.mm"
include "simp1d.mm"
include "resubcl.mm"
include "sylancr.mm"
include "leidd.mm"
include "1red.mm"
include "simp3d.mm"
include "abssubge0d.mm"
include "simp2d.mm"
include "absidd.mm"
include "oveq2d.mm"
include "recnd.mm"
include "mulid2d.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "ssrabdv.mm"
include "resmptd.mm"
include "syl6eqr.mm"
include "0le1.mm"
include "eqid.mm"
include "abelth.mm"
include "rescncf.mm"
include "sylc.mm"
include "eqeltrrd.mm"

theorem abelth2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cF: class F
  let vz: setvar z
  assume abelth2.1: |- ( ph -> A : NN0 --> CC )
  assume abelth2.2: |- ( ph -> seq 0 ( + , A ) e. dom ~~> )
  assume abelth2.3: |- F = ( x e. ( 0 [,] 1 ) |-> sum_ n e. NN0 ( ( A ` n ) x. ( x ^ n ) ) )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint n ph
  disjoint ph x
  disjoint n z
  disjoint x z
  disjoint A z
  disjoint ph z
  assert |- ( ph -> F e. ( ( 0 [,] 1 ) -cn-> CC ) )

  proof
    wph
    vx
    c1
    vz
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    c1
    @0
    cabs
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    vz
    cc
    crab
    #
    cn0
    vn
    cv
    #
    cA
    cfv
    vx
    cv
    @8
    cexp
    co
    cmul
    co
    vn
    csu
    #
    cmpt
    #
    cc0
    c1
    cicc
    co
    #
    cres
    #
    cF
    @11
    cc
    ccncf
    co
    #
    wph
    @12
    vx
    @11
    @9
    cmpt
    cF
    wph
    vx
    @7
    @11
    @9
    wph
    @6
    vz
    cc
    @11
    @11
    cc
    wss
    wph
    @11
    cr
    cc
    unitssre
    ax-resscn
    sstri
    a1i
    wph
    @0
    @11
    wcel
    #
    wa
    #
    @1
    @1
    @2
    @5
    cle
    @15
    @1
    @15
    c1
    cr
    wcel
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    1re
    @15
    @16
    cc0
    @0
    cle
    wbr
    #
    @0
    c1
    cle
    wbr
    #
    @15
    @14
    @16
    @17
    @18
    w3a
    wph
    @14
    simpr
    cc0
    c1
    @0
    0re
    1re
    elicc2i
    sylib
    #
    simp1d
    #
    c1
    @0
    resubcl
    sylancr
    #
    leidd
    @15
    @0
    c1
    @20
    @15
    1red
    @15
    @16
    @17
    @18
    @19
    simp3d
    abssubge0d
    @15
    @5
    c1
    @1
    cmul
    co
    @1
    @15
    @4
    @1
    c1
    cmul
    @15
    @3
    @0
    c1
    cmin
    @15
    @0
    @20
    @15
    @16
    @17
    @18
    @19
    simp2d
    absidd
    oveq2d
    oveq2d
    @15
    @1
    @15
    @1
    @21
    recnd
    mulid2d
    eqtrd
    3brtr4d
    ssrabdv
    #
    resmptd
    abelth2.3
    syl6eqr
    wph
    @11
    @7
    wss
    @10
    @7
    cc
    ccncf
    co
    wcel
    @12
    @13
    wcel
    @22
    wph
    vx
    vz
    cA
    @7
    vn
    @10
    c1
    abelth2.1
    abelth2.2
    wph
    1red
    cc0
    c1
    cle
    wbr
    wph
    0le1
    a1i
    @7
    eqid
    @10
    eqid
    abelth
    @7
    cc
    @11
    @10
    rescncf
    sylc
    eqeltrrd
end
