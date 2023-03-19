include "cv.mm"
include "cdm.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cuni.mm"
include "cpw.mm"
include "wceq.mm"
include "wa.mm"
include "c0.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "cres.mm"
include "csumge0.mm"
include "wi.mm"
include "come.mm"
include "id.mm"
include "dmeq.mm"
include "feq12d.mm"
include "unieqd.mm"
include "pweqd.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "breq12d.mm"
include "ralbidv.mm"
include "raleqbidv.mm"
include "reseq1.mm"
include "fveq2d.mm"
include "imbi2d.mm"
include "df-ome.mm"
include "elab2g.mm"

theorem isome
  let vy: setvar y
  let vz: setvar z
  let cO: class O
  let cV: class V
  let vx: setvar x
  let vk: setvar k

  disjoint O y
  disjoint O z
  disjoint y z
  disjoint O x
  disjoint x y
  disjoint x z
  disjoint k x
  assert |- ( O e. V -> ( O e. OutMeas <-> ( ( ( ( O : dom O --> ( 0 [,] +oo ) /\ dom O = ~P U. dom O ) /\ ( O ` (/) ) = 0 ) /\ A. y e. ~P U. dom O A. z e. ~P y ( O ` z ) <_ ( O ` y ) ) /\ A. y e. ~P dom O ( y ~<_ _om -> ( O ` U. y ) <_ ( sum^ ` ( O |` y ) ) ) ) ) )

  proof
    vx
    cv
    #
    cdm
    #
    cc0
    cpnf
    cicc
    co
    #
    @0
    wf
    #
    @1
    @1
    cuni
    #
    cpw
    #
    wceq
    #
    wa
    #
    c0
    @0
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vz
    cv
    #
    @0
    cfv
    #
    vy
    cv
    #
    @0
    cfv
    #
    cle
    wbr
    #
    vz
    @13
    cpw
    #
    wral
    #
    vy
    @5
    wral
    #
    wa
    #
    @13
    com
    cdom
    wbr
    #
    @13
    cuni
    #
    @0
    cfv
    #
    @0
    @13
    cres
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vy
    @1
    cpw
    #
    wral
    #
    wa
    cO
    cdm
    #
    @2
    cO
    wf
    #
    @29
    @29
    cuni
    #
    cpw
    #
    wceq
    #
    wa
    #
    c0
    cO
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    @11
    cO
    cfv
    #
    @13
    cO
    cfv
    #
    cle
    wbr
    #
    vz
    @16
    wral
    #
    vy
    @32
    wral
    #
    wa
    #
    @20
    @21
    cO
    cfv
    #
    cO
    @13
    cres
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vy
    @29
    cpw
    #
    wral
    #
    wa
    vx
    cO
    come
    cV
    @0
    cO
    wceq
    #
    @19
    @43
    @28
    @50
    @51
    @10
    @37
    @18
    @42
    @51
    @7
    @34
    @9
    @36
    @51
    @3
    @30
    @6
    @33
    @51
    @1
    @29
    @2
    @0
    cO
    @51
    id
    @0
    cO
    dmeq
    #
    feq12d
    @51
    @1
    @29
    @5
    @32
    @52
    @51
    @4
    @31
    @51
    @1
    @29
    @52
    unieqd
    pweqd
    #
    eqeq12d
    anbi12d
    @51
    @8
    @35
    cc0
    c0
    @0
    cO
    fveq1
    eqeq1d
    anbi12d
    @51
    @17
    @41
    vy
    @5
    @32
    @53
    @51
    @15
    @40
    vz
    @16
    @51
    @12
    @38
    @14
    @39
    cle
    @11
    @0
    cO
    fveq1
    @13
    @0
    cO
    fveq1
    breq12d
    ralbidv
    raleqbidv
    anbi12d
    @51
    @26
    @48
    vy
    @27
    @49
    @51
    @1
    @29
    @52
    pweqd
    @51
    @25
    @47
    @20
    @51
    @22
    @44
    @24
    @46
    cle
    @21
    @0
    cO
    fveq1
    @51
    @23
    @45
    csumge0
    @0
    cO
    @13
    reseq1
    fveq2d
    breq12d
    imbi2d
    raleqbidv
    anbi12d
    vx
    vy
    vz
    df-ome
    elab2g
end
