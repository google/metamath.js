include "caddc.mm"
include "cn.mm"
include "cfv.mm"
include "c1.mm"
include "cseq.mm"
include "c3.mm"
include "cdiv.mm"
include "co.mm"
include "cexp.mm"
include "cmin.mm"
include "c2.mm"
include "cli.mm"
include "wbr.mm"
include "wtru.mm"
include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "1re.mm"
include "3nn.mm"
include "nndivre.mm"
include "mp2an.mm"
include "recni.mm"
include "a1i.mm"
include "cabs.mm"
include "clt.mm"
include "cc0.mm"
include "cle.mm"
include "wceq.mm"
include "0re.mm"
include "3re.mm"
include "3pos.mm"
include "recgt0ii.mm"
include "ltleii.mm"
include "absid.mm"
include "1lt3.mm"
include "wb.mm"
include "recgt1.mm"
include "mpbi.mm"
include "eqbrtri.mm"
include "cn0.mm"
include "1nn0.mm"
include "cv.mm"
include "cuz.mm"
include "wa.mm"
include "cif.mm"
include "wss.mm"
include "ssid.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleqr.mm"
include "rpnnen2lem1.mm"
include "sylancr.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "geolim2.mm"
include "trud.mm"
include "exp1.mm"
include "ax-mp.mm"
include "wne.mm"
include "3cn.mm"
include "ax-1cn.mm"
include "3ne0.mm"
include "pm3.2i.mm"
include "divsubdir.mm"
include "mp3an.mm"
include "3m1e2.mm"
include "oveq1i.mm"
include "dividi.mm"
include "3eqtr3ri.mm"
include "oveq12i.mm"
include "2cnne0.mm"
include "divcan7.mm"
include "eqtri.mm"
include "breqtri.mm"

theorem rpnnen2lem3
  let vx: setvar x
  let vn: setvar n
  let cF: class F
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let cA: class A
  let cB: class B
  let wph: wff ph
  let cM: class M
  let cN: class N
  assume rpnnen2.1: |- F = ( x e. ~P NN |-> ( n e. NN |-> if ( n e. x , ( ( 1 / 3 ) ^ n ) , 0 ) ) )

  disjoint n x
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint A n
  disjoint A x
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint F m
  disjoint F y
  disjoint F z
  disjoint k ph
  disjoint M k
  disjoint M n
  disjoint M x
  disjoint N n
  assert |- seq 1 ( + , ( F ` NN ) ) ~~> ( 1 / 2 )

  proof
    caddc
    cn
    cF
    cfv
    #
    c1
    cseq
    #
    c1
    c3
    cdiv
    co
    #
    c1
    cexp
    co
    #
    c1
    @2
    cmin
    co
    #
    cdiv
    co
    #
    c1
    c2
    cdiv
    co
    #
    cli
    @1
    @5
    cli
    wbr
    wtru
    @2
    vk
    @0
    c1
    @2
    cc
    wcel
    #
    wtru
    @2
    c1
    cr
    wcel
    c3
    cn
    wcel
    @2
    cr
    wcel
    #
    1re
    3nn
    c1
    c3
    nndivre
    mp2an
    #
    recni
    #
    a1i
    @2
    cabs
    cfv
    #
    c1
    clt
    wbr
    wtru
    @11
    @2
    c1
    clt
    @8
    cc0
    @2
    cle
    wbr
    @11
    @2
    wceq
    @9
    cc0
    @2
    0re
    @9
    c3
    3re
    3pos
    recgt0ii
    ltleii
    @2
    absid
    mp2an
    c1
    c3
    clt
    wbr
    #
    @2
    c1
    clt
    wbr
    #
    1lt3
    c3
    cr
    wcel
    cc0
    c3
    clt
    wbr
    @12
    @13
    wb
    3re
    3pos
    c3
    recgt1
    mp2an
    mpbi
    eqbrtri
    a1i
    c1
    cn0
    wcel
    wtru
    1nn0
    a1i
    wtru
    vk
    cv
    #
    c1
    cuz
    cfv
    #
    wcel
    #
    wa
    #
    @14
    @0
    cfv
    #
    @14
    cn
    wcel
    #
    @2
    @14
    cexp
    co
    #
    cc0
    cif
    #
    @20
    @17
    cn
    cn
    wss
    @19
    @18
    @21
    wceq
    cn
    ssid
    @17
    @14
    @15
    cn
    wtru
    @16
    simpr
    nnuz
    syl6eleqr
    #
    vx
    cn
    vn
    cF
    @14
    rpnnen2.1
    rpnnen2lem1
    sylancr
    @17
    @19
    @20
    cc0
    @22
    iftrued
    eqtrd
    geolim2
    trud
    @5
    @2
    c2
    c3
    cdiv
    co
    #
    cdiv
    co
    #
    @6
    @3
    @2
    @4
    @23
    cdiv
    @7
    @3
    @2
    wceq
    @10
    @2
    exp1
    ax-mp
    c3
    c1
    cmin
    co
    #
    c3
    cdiv
    co
    #
    c3
    c3
    cdiv
    co
    #
    @2
    cmin
    co
    #
    @23
    @4
    c3
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @29
    c3
    cc0
    wne
    #
    wa
    #
    @26
    @28
    wceq
    3cn
    ax-1cn
    @29
    @31
    3cn
    3ne0
    pm3.2i
    #
    c3
    c1
    c3
    divsubdir
    mp3an
    @25
    c2
    c3
    cdiv
    3m1e2
    oveq1i
    @27
    c1
    @2
    cmin
    c3
    3cn
    3ne0
    dividi
    oveq1i
    3eqtr3ri
    oveq12i
    @30
    c2
    cc
    wcel
    c2
    cc0
    wne
    wa
    @32
    @24
    @6
    wceq
    ax-1cn
    2cnne0
    @33
    c1
    c2
    c3
    divcan7
    mp3an
    eqtri
    breqtri
end
