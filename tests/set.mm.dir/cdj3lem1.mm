include "cc0.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cno.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cva.mm"
include "cmul.mm"
include "cle.mm"
include "wral.mm"
include "wa.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "cr.mm"
include "wcel.mm"
include "wss.mm"
include "c0v.mm"
include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "wi.mm"
include "elin.mm"
include "csh.mm"
include "cc.mm"
include "neg1cn.mm"
include "shmulcl.mm"
include "mp3an12.mm"
include "anim2i.mm"
include "sylbi.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "syl.mm"
include "adantl.mm"
include "chil.mm"
include "wb.mm"
include "shincli.mm"
include "sheli.mm"
include "c2.mm"
include "normneg.mm"
include "normcl.mm"
include "recnd.mm"
include "2timesd.mm"
include "eqtr4d.mm"
include "hvnegid.mm"
include "norm0.mm"
include "syl6eq.mm"
include "recn.mm"
include "mul01d.mm"
include "sylan9eqr.mm"
include "2t0e0.mm"
include "syl6eqr.mm"
include "0re.mm"
include "letri3.mm"
include "sylancl.mm"
include "normge0.mm"
include "biantrud.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lemul2.mm"
include "mp3an23.mm"
include "3bitr2rd.mm"
include "norm-i.mm"
include "bitrd.mm"
include "sylan2.mm"
include "sylibd.mm"
include "impancom.mm"
include "elch0.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "ex.mm"
include "shle0.mm"
include "ax-mp.mm"
include "syl6ib.mm"
include "adantld.mm"
include "rexlimiv.mm"

theorem cdj3lem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vv: setvar v
  assume cdj1.1: |- A e. SH
  assume cdj1.2: |- B e. SH

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint v w
  disjoint B w
  disjoint B v
  assert |- ( E. x e. RR ( 0 < x /\ A. y e. A A. z e. B ( ( normh ` y ) + ( normh ` z ) ) <_ ( x x. ( normh ` ( y +h z ) ) ) ) -> ( A i^i B ) = 0H )

  proof
    cc0
    vx
    cv
    #
    clt
    wbr
    #
    vy
    cv
    #
    cno
    cfv
    #
    vz
    cv
    #
    cno
    cfv
    #
    caddc
    co
    #
    @0
    @2
    @4
    cva
    co
    #
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vz
    cB
    wral
    vy
    cA
    wral
    #
    wa
    cA
    cB
    cin
    #
    c0h
    wceq
    #
    vx
    cr
    @0
    cr
    wcel
    #
    @11
    @13
    @1
    @14
    @11
    @12
    c0h
    wss
    #
    @13
    @14
    @11
    @15
    @14
    @11
    wa
    #
    vw
    @12
    c0h
    @16
    vw
    cv
    #
    @12
    wcel
    #
    @17
    c0v
    wceq
    #
    @17
    c0h
    wcel
    @14
    @18
    @11
    @19
    @14
    @18
    wa
    @11
    @17
    cno
    cfv
    #
    c1
    cneg
    #
    @17
    csm
    co
    #
    cno
    cfv
    #
    caddc
    co
    #
    @0
    @17
    @22
    cva
    co
    #
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @19
    @18
    @11
    @28
    wi
    #
    @14
    @18
    @17
    cA
    wcel
    #
    @22
    cB
    wcel
    #
    wa
    #
    @29
    @18
    @30
    @17
    cB
    wcel
    #
    wa
    @32
    @17
    cA
    cB
    elin
    @33
    @31
    @30
    cB
    csh
    wcel
    @21
    cc
    wcel
    @33
    @31
    cdj1.2
    neg1cn
    @21
    @17
    cB
    shmulcl
    mp3an12
    anim2i
    sylbi
    @10
    @28
    @20
    @5
    caddc
    co
    #
    @0
    @17
    @4
    cva
    co
    #
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    vy
    vz
    @17
    @22
    cA
    cB
    @2
    @17
    wceq
    #
    @6
    @34
    @9
    @37
    cle
    @38
    @3
    @20
    @5
    caddc
    @2
    @17
    cno
    fveq2
    oveq1d
    @38
    @8
    @36
    @0
    cmul
    @38
    @7
    @35
    cno
    @2
    @17
    @4
    cva
    oveq1
    fveq2d
    oveq2d
    breq12d
    @4
    @22
    wceq
    #
    @34
    @24
    @37
    @27
    cle
    @39
    @5
    @23
    @20
    caddc
    @4
    @22
    cno
    fveq2
    oveq2d
    @39
    @36
    @26
    @0
    cmul
    @39
    @35
    @25
    cno
    @4
    @22
    @17
    cva
    oveq2
    fveq2d
    oveq2d
    breq12d
    rspc2v
    syl
    adantl
    @18
    @14
    @17
    chil
    wcel
    #
    @28
    @19
    wb
    @17
    @12
    cA
    cB
    cdj1.1
    cdj1.2
    shincli
    #
    sheli
    @14
    @40
    wa
    #
    @28
    c2
    @20
    cmul
    co
    #
    c2
    cc0
    cmul
    co
    #
    cle
    wbr
    #
    @19
    @42
    @24
    @43
    @27
    @44
    cle
    @40
    @24
    @43
    wceq
    @14
    @40
    @24
    @20
    @20
    caddc
    co
    @43
    @40
    @23
    @20
    @20
    caddc
    @17
    normneg
    oveq2d
    @40
    @20
    @40
    @20
    @17
    normcl
    #
    recnd
    2timesd
    eqtr4d
    adantl
    @42
    @27
    cc0
    @44
    @40
    @14
    @27
    @0
    cc0
    cmul
    co
    cc0
    @40
    @26
    cc0
    @0
    cmul
    @40
    @26
    c0v
    cno
    cfv
    cc0
    @40
    @25
    c0v
    cno
    @17
    hvnegid
    fveq2d
    norm0
    syl6eq
    oveq2d
    @14
    @0
    @0
    recn
    mul01d
    sylan9eqr
    2t0e0
    syl6eqr
    breq12d
    @40
    @45
    @19
    wb
    @14
    @40
    @45
    @20
    cc0
    wceq
    #
    @19
    @40
    @47
    @20
    cc0
    cle
    wbr
    #
    cc0
    @20
    cle
    wbr
    #
    wa
    #
    @48
    @45
    @40
    @20
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @47
    @50
    wb
    @46
    0re
    @20
    cc0
    letri3
    sylancl
    @40
    @49
    @48
    @17
    normge0
    biantrud
    @40
    @51
    @48
    @45
    wb
    #
    @46
    @51
    @52
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    @53
    0re
    @54
    @55
    2re
    2pos
    pm3.2i
    @20
    cc0
    c2
    lemul2
    mp3an23
    syl
    3bitr2rd
    @17
    norm-i
    bitrd
    adantl
    bitrd
    sylan2
    sylibd
    impancom
    @17
    elch0
    syl6ibr
    ssrdv
    ex
    @12
    csh
    wcel
    @15
    @13
    wb
    @41
    @12
    shle0
    ax-mp
    syl6ib
    adantld
    rexlimiv
end
