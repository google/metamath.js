include "com.mm"
include "wcel.mm"
include "coa.mm"
include "co.mm"
include "cfv.mm"
include "caddc.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "c0.mm"
include "csuc.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "cc0.mm"
include "cn0.mm"
include "wf1o.mm"
include "wf.mm"
include "hashgf1o.mm"
include "f1of.mm"
include "ax-mp.mm"
include "ffvelrni.mm"
include "nn0cnd.mm"
include "addid1d.mm"
include "0z.mm"
include "om2uz0i.mm"
include "oveq2i.mm"
include "a1i.mm"
include "nna0.mm"
include "3eqtr4rd.mm"
include "w3a.mm"
include "c1.mm"
include "wa.mm"
include "nnasuc.mm"
include "nnacl.mm"
include "om2uzsuci.mm"
include "syl.mm"
include "eqtrd.mm"
include "3adant3.mm"
include "cc.mm"
include "ax-1cn.mm"
include "addass.mm"
include "mp3an3.mm"
include "syl2an.mm"
include "oveq1.mm"
include "3ad2ant3.mm"
include "3ad2ant2.mm"
include "3eqtr4d.mm"
include "3expia.mm"
include "expcom.mm"
include "a2d.mm"
include "finds.mm"
include "impcom.mm"

theorem hashgadd
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cG: class G
  let vn: setvar n
  let vz: setvar z
  assume hashgadd.1: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , 0 ) |` _om )


  assert |- ( ( A e. _om /\ B e. _om ) -> ( G ` ( A +o B ) ) = ( ( G ` A ) + ( G ` B ) ) )

  proof
    cB
    com
    wcel
    cA
    com
    wcel
    #
    cA
    cB
    coa
    co
    #
    cG
    cfv
    #
    cA
    cG
    cfv
    #
    cB
    cG
    cfv
    #
    caddc
    co
    #
    wceq
    #
    @0
    cA
    vn
    cv
    #
    coa
    co
    #
    cG
    cfv
    #
    @3
    @7
    cG
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    @0
    cA
    c0
    coa
    co
    #
    cG
    cfv
    #
    @3
    c0
    cG
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    @0
    cA
    vz
    cv
    #
    coa
    co
    #
    cG
    cfv
    #
    @3
    @18
    cG
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    @0
    cA
    @18
    csuc
    #
    coa
    co
    #
    cG
    cfv
    #
    @3
    @24
    cG
    cfv
    #
    caddc
    co
    #
    wceq
    #
    wi
    @0
    @6
    wi
    vn
    vz
    cB
    @7
    c0
    wceq
    #
    @12
    @17
    @0
    @30
    @9
    @14
    @11
    @16
    @30
    @8
    @13
    cG
    @7
    c0
    cA
    coa
    oveq2
    fveq2d
    @30
    @10
    @15
    @3
    caddc
    @7
    c0
    cG
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @7
    @18
    wceq
    #
    @12
    @23
    @0
    @31
    @9
    @20
    @11
    @22
    @31
    @8
    @19
    cG
    @7
    @18
    cA
    coa
    oveq2
    fveq2d
    @31
    @10
    @21
    @3
    caddc
    @7
    @18
    cG
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @7
    @24
    wceq
    #
    @12
    @29
    @0
    @32
    @9
    @26
    @11
    @28
    @32
    @8
    @25
    cG
    @7
    @24
    cA
    coa
    oveq2
    fveq2d
    @32
    @10
    @27
    @3
    caddc
    @7
    @24
    cG
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @7
    cB
    wceq
    #
    @12
    @6
    @0
    @33
    @9
    @2
    @11
    @5
    @33
    @8
    @1
    cG
    @7
    cB
    cA
    coa
    oveq2
    fveq2d
    @33
    @10
    @4
    @3
    caddc
    @7
    cB
    cG
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @0
    @3
    cc0
    caddc
    co
    #
    @3
    @16
    @14
    @0
    @3
    @0
    @3
    com
    cn0
    cA
    cG
    com
    cn0
    cG
    wf1o
    com
    cn0
    cG
    wf
    vx
    cG
    hashgadd.1
    hashgf1o
    com
    cn0
    cG
    f1of
    ax-mp
    #
    ffvelrni
    nn0cnd
    #
    addid1d
    @16
    @34
    wceq
    @0
    @15
    cc0
    @3
    caddc
    vx
    cc0
    cG
    0z
    hashgadd.1
    om2uz0i
    oveq2i
    a1i
    @0
    @13
    cA
    cG
    cA
    nna0
    fveq2d
    3eqtr4rd
    @18
    com
    wcel
    #
    @0
    @23
    @29
    @0
    @37
    @23
    @29
    wi
    @0
    @37
    @23
    @29
    @0
    @37
    @23
    w3a
    #
    @26
    @20
    c1
    caddc
    co
    #
    @28
    @0
    @37
    @26
    @39
    wceq
    @23
    @0
    @37
    wa
    #
    @26
    @19
    csuc
    #
    cG
    cfv
    #
    @39
    @40
    @25
    @41
    cG
    cA
    @18
    nnasuc
    fveq2d
    @40
    @19
    com
    wcel
    @42
    @39
    wceq
    cA
    @18
    nnacl
    vx
    @19
    cc0
    cG
    0z
    hashgadd.1
    om2uzsuci
    syl
    eqtrd
    3adant3
    @38
    @22
    c1
    caddc
    co
    #
    @3
    @21
    c1
    caddc
    co
    #
    caddc
    co
    #
    @39
    @28
    @0
    @37
    @43
    @45
    wceq
    #
    @23
    @0
    @3
    cc
    wcel
    #
    @21
    cc
    wcel
    #
    @46
    @37
    @36
    @37
    @21
    com
    cn0
    @18
    cG
    @35
    ffvelrni
    nn0cnd
    @47
    @48
    c1
    cc
    wcel
    @46
    ax-1cn
    @3
    @21
    c1
    addass
    mp3an3
    syl2an
    3adant3
    @23
    @0
    @39
    @43
    wceq
    @37
    @20
    @22
    c1
    caddc
    oveq1
    3ad2ant3
    @37
    @0
    @28
    @45
    wceq
    @23
    @37
    @27
    @44
    @3
    caddc
    vx
    @18
    cc0
    cG
    0z
    hashgadd.1
    om2uzsuci
    oveq2d
    3ad2ant2
    3eqtr4d
    eqtrd
    3expia
    expcom
    a2d
    finds
    impcom
end
