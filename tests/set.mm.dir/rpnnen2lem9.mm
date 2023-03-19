include "cn.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "csu.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "c3.mm"
include "cdiv.mm"
include "cexp.mm"
include "cmin.mm"
include "eqid.mm"
include "nnz.mm"
include "wa.mm"
include "eqidd.mm"
include "cc.mm"
include "eluznn.mm"
include "cr.mm"
include "wss.mm"
include "wf.mm"
include "difss.mm"
include "rpnnen2lem2.mm"
include "ax-mp.mm"
include "ffvelrni.mm"
include "recnd.mm"
include "syl.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "rpnnen2lem5.mm"
include "mpan.mm"
include "isum1p.mm"
include "cif.mm"
include "wceq.mm"
include "rpnnen2lem1.mm"
include "neldifsnd.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "peano2nn.mm"
include "nnzd.mm"
include "sylan.mm"
include "1re.mm"
include "3nn.mm"
include "nndivre.mm"
include "mp2an.mm"
include "recni.mm"
include "a1i.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
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
include "nnnn0d.mm"
include "wne.mm"
include "nnre.mm"
include "adantr.mm"
include "eluzle.mm"
include "adantl.mm"
include "nnltp1le.mm"
include "syldan.mm"
include "mpbird.mm"
include "gtned.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "iftrued.mm"
include "geolim2.mm"
include "isumclim.mm"
include "oveq12d.mm"

theorem rpnnen2lem9
  let vx: setvar x
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let vm: setvar m
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let wph: wff ph
  let cN: class N
  assume rpnnen2.1: |- F = ( x e. ~P NN |-> ( n e. NN |-> if ( n e. x , ( ( 1 / 3 ) ^ n ) , 0 ) ) )

  disjoint n x
  disjoint k n
  disjoint k x
  disjoint F k
  disjoint M k
  disjoint M n
  disjoint M x
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint n y
  disjoint n z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A k
  disjoint A n
  disjoint A x
  disjoint B k
  disjoint B n
  disjoint B x
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint F m
  disjoint F y
  disjoint F z
  disjoint k ph
  disjoint N n
  assert |- ( M e. NN -> sum_ k e. ( ZZ>= ` M ) ( ( F ` ( NN \ { M } ) ) ` k ) = ( 0 + ( ( ( 1 / 3 ) ^ ( M + 1 ) ) / ( 1 - ( 1 / 3 ) ) ) ) )

  proof
    cM
    cn
    wcel
    #
    cM
    cuz
    cfv
    #
    vk
    cv
    #
    cn
    cM
    csn
    #
    cdif
    #
    cF
    cfv
    #
    cfv
    #
    vk
    csu
    cM
    @5
    cfv
    #
    cM
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @6
    vk
    csu
    #
    caddc
    co
    cc0
    c1
    c3
    cdiv
    co
    #
    @8
    cexp
    co
    c1
    @11
    cmin
    co
    cdiv
    co
    #
    caddc
    co
    @0
    @6
    vk
    @5
    cM
    @1
    @1
    eqid
    cM
    nnz
    @0
    @2
    @1
    wcel
    wa
    #
    @6
    eqidd
    @13
    @2
    cn
    wcel
    #
    @6
    cc
    wcel
    #
    @2
    cM
    eluznn
    @14
    @6
    cn
    cr
    @2
    @5
    @4
    cn
    wss
    #
    cn
    cr
    @5
    wf
    cn
    @3
    difss
    #
    vx
    @4
    vn
    cF
    rpnnen2.1
    rpnnen2lem2
    ax-mp
    ffvelrni
    recnd
    #
    syl
    @16
    @0
    caddc
    @5
    cM
    cseq
    cli
    cdm
    wcel
    @17
    vx
    @4
    vn
    cF
    cM
    rpnnen2.1
    rpnnen2lem5
    mpan
    isum1p
    @0
    @7
    cc0
    @10
    @12
    caddc
    @0
    @7
    cM
    @4
    wcel
    #
    @11
    cM
    cexp
    co
    #
    cc0
    cif
    #
    cc0
    @16
    @0
    @7
    @21
    wceq
    @17
    vx
    @4
    vn
    cF
    cM
    rpnnen2.1
    rpnnen2lem1
    mpan
    @0
    @19
    @20
    cc0
    @0
    cM
    cn
    neldifsnd
    iffalsed
    eqtrd
    @0
    @6
    @12
    vk
    @5
    @8
    @9
    @9
    eqid
    @0
    @8
    cM
    peano2nn
    #
    nnzd
    @0
    @2
    @9
    wcel
    #
    wa
    #
    @6
    eqidd
    @24
    @14
    @15
    @0
    @8
    cn
    wcel
    @23
    @14
    @22
    @2
    @8
    eluznn
    sylan
    #
    @18
    syl
    @0
    @11
    vk
    @5
    @8
    @11
    cc
    wcel
    @0
    @11
    c1
    cr
    wcel
    c3
    cn
    wcel
    @11
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
    a1i
    @11
    cabs
    cfv
    #
    c1
    clt
    wbr
    @0
    @28
    @11
    c1
    clt
    @26
    cc0
    @11
    cle
    wbr
    @28
    @11
    wceq
    @27
    cc0
    @11
    0re
    @27
    c3
    3re
    3pos
    recgt0ii
    ltleii
    @11
    absid
    mp2an
    c1
    c3
    clt
    wbr
    #
    @11
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
    @29
    @30
    wb
    3re
    3pos
    c3
    recgt1
    mp2an
    mpbi
    eqbrtri
    a1i
    @0
    @8
    @22
    nnnn0d
    @24
    @6
    @2
    @4
    wcel
    #
    @11
    @2
    cexp
    co
    #
    cc0
    cif
    #
    @32
    @24
    @14
    @6
    @33
    wceq
    #
    @25
    @16
    @14
    @34
    @17
    vx
    @4
    vn
    cF
    @2
    rpnnen2.1
    rpnnen2lem1
    mpan
    syl
    @24
    @31
    @32
    cc0
    @24
    @14
    @2
    cM
    wne
    @31
    @25
    @24
    cM
    @2
    @0
    cM
    cr
    wcel
    @23
    cM
    nnre
    adantr
    @24
    cM
    @2
    clt
    wbr
    #
    @8
    @2
    cle
    wbr
    #
    @23
    @36
    @0
    @8
    @2
    eluzle
    adantl
    @0
    @23
    @14
    @35
    @36
    wb
    @25
    cM
    @2
    nnltp1le
    syldan
    mpbird
    gtned
    @2
    cn
    cM
    eldifsn
    sylanbrc
    iftrued
    eqtrd
    geolim2
    isumclim
    oveq12d
    eqtrd
end
