include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "cgcd.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cfzo.mm"
include "crab.mm"
include "chash.mm"
include "cfv.mm"
include "cdiv.mm"
include "cphi.mm"
include "cif.mm"
include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "eqeq2.mm"
include "c1.mm"
include "nndivdvds.mm"
include "biimpa.mm"
include "dfphi2.mm"
include "syl.mm"
include "cmul.mm"
include "cmpt.mm"
include "wf1o.mm"
include "cen.mm"
include "eqid.mm"
include "hashgcdlem.mm"
include "3expa.mm"
include "ovex.mm"
include "rabex.mm"
include "f1oen.mm"
include "hasheni.mm"
include "3syl.mm"
include "eqtr2d.mm"
include "wn.mm"
include "c0.mm"
include "wral.mm"
include "simprr.mm"
include "cz.mm"
include "elfzoelz.mm"
include "ad2antrl.mm"
include "nnz.mm"
include "ad2antrr.mm"
include "gcddvds.mm"
include "syl2anc.mm"
include "simprd.mm"
include "eqbrtrrd.mm"
include "expr.mm"
include "con3d.mm"
include "impancom.mm"
include "ralrimiv.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "fveq2d.mm"
include "hash0.mm"
include "syl6eq.mm"
include "ifbothda.mm"

theorem hashgcdeq
  let vx: setvar x
  let cM: class M
  let cN: class N
  let vz: setvar z
  let vy: setvar y

  disjoint M x
  disjoint N x
  disjoint x z
  disjoint M z
  disjoint N z
  disjoint y z
  disjoint M y
  disjoint N y
  assert |- ( ( M e. NN /\ N e. NN ) -> ( # ` { x e. ( 0 ..^ M ) | ( x gcd M ) = N } ) = if ( N || M , ( phi ` ( M / N ) ) , 0 ) )

  proof
    cN
    cM
    cdvds
    wbr
    #
    vx
    cv
    #
    cM
    cgcd
    co
    #
    cN
    wceq
    #
    vx
    cc0
    cM
    cfzo
    co
    #
    crab
    #
    chash
    cfv
    #
    cM
    cN
    cdiv
    co
    #
    cphi
    cfv
    #
    wceq
    @6
    cc0
    wceq
    @6
    @0
    @8
    cc0
    cif
    #
    wceq
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    @8
    cc0
    @8
    @9
    @6
    eqeq2
    cc0
    @9
    @6
    eqeq2
    @12
    @0
    wa
    #
    @8
    vy
    cv
    @7
    cgcd
    co
    c1
    wceq
    #
    vy
    cc0
    @7
    cfzo
    co
    #
    crab
    #
    chash
    cfv
    #
    @6
    @13
    @7
    cn
    wcel
    #
    @8
    @17
    wceq
    @12
    @0
    @18
    cM
    cN
    nndivdvds
    biimpa
    vy
    @7
    dfphi2
    syl
    @13
    @16
    @5
    vz
    @16
    vz
    cv
    cN
    cmul
    co
    cmpt
    #
    wf1o
    #
    @16
    @5
    cen
    wbr
    @17
    @6
    wceq
    @10
    @11
    @0
    @20
    vz
    vy
    vx
    @16
    @5
    @19
    cM
    cN
    @16
    eqid
    @5
    eqid
    @19
    eqid
    hashgcdlem
    3expa
    @16
    @5
    @19
    @14
    vy
    @15
    cc0
    @7
    cfzo
    ovex
    rabex
    f1oen
    @16
    @5
    hasheni
    3syl
    eqtr2d
    @12
    @0
    wn
    #
    wa
    #
    @6
    c0
    chash
    cfv
    cc0
    @22
    @5
    c0
    chash
    @22
    @3
    wn
    #
    vx
    @4
    wral
    @5
    c0
    wceq
    @22
    @23
    vx
    @4
    @12
    @1
    @4
    wcel
    #
    @21
    @23
    @12
    @24
    wa
    @3
    @0
    @12
    @24
    @3
    @0
    @12
    @24
    @3
    wa
    #
    wa
    #
    @2
    cN
    cM
    cdvds
    @12
    @24
    @3
    simprr
    @26
    @2
    @1
    cdvds
    wbr
    #
    @2
    cM
    cdvds
    wbr
    #
    @26
    @1
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @27
    @28
    wa
    @24
    @29
    @12
    @3
    @1
    cc0
    cM
    elfzoelz
    ad2antrl
    @10
    @30
    @11
    @25
    cM
    nnz
    ad2antrr
    @1
    cM
    gcddvds
    syl2anc
    simprd
    eqbrtrrd
    expr
    con3d
    impancom
    ralrimiv
    @3
    vx
    @4
    rabeq0
    sylibr
    fveq2d
    hash0
    syl6eq
    ifbothda
end
