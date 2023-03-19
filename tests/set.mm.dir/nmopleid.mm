include "cho.mm"
include "wcel.mm"
include "cnop.mm"
include "cfv.mm"
include "cr.mm"
include "ch0o.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "chot.mm"
include "chio.mm"
include "cleo.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "clo.mm"
include "hmoplin.mm"
include "nmlnopne0.mm"
include "biimpar.mm"
include "sylan.mm"
include "adantlr.mm"
include "cle.mm"
include "rereccl.mm"
include "adantll.mm"
include "simpll.mm"
include "idhmop.mm"
include "hmopm.mm"
include "mpan2.mm"
include "ad2antlr.mm"
include "clt.mm"
include "simplr.mm"
include "chil.mm"
include "wf.mm"
include "hmopf.mm"
include "nmopgt0.mm"
include "biimpa.mm"
include "recgt0d.mm"
include "wi.mm"
include "0re.mm"
include "ltle.mm"
include "sylancr.mm"
include "mpd.mm"
include "leopnmid.mm"
include "adantr.mm"
include "leopmul2i.mm"
include "syl32anc.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "cmul.mm"
include "reccl.mm"
include "simpl.mm"
include "wf1o.mm"
include "hoif.mm"
include "f1of.mm"
include "ax-mp.mm"
include "homulass.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "recid2.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "homulid2.mm"
include "syl6eq.mm"
include "breqtrd.mm"
include "syldan.mm"
include "3impa.mm"

theorem nmopleid
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cU: class U


  assert |- ( ( T e. HrmOp /\ ( normop ` T ) e. RR /\ T =/= 0hop ) -> ( ( 1 / ( normop ` T ) ) .op T ) <_op Iop )

  proof
    cT
    cho
    wcel
    #
    cT
    cnop
    cfv
    #
    cr
    wcel
    #
    cT
    ch0o
    wne
    #
    c1
    @1
    cdiv
    co
    #
    cT
    chot
    co
    #
    chio
    cleo
    wbr
    #
    @0
    @2
    wa
    #
    @3
    @1
    cc0
    wne
    #
    @6
    @0
    @3
    @8
    @2
    @0
    cT
    clo
    wcel
    #
    @3
    @8
    cT
    hmoplin
    @9
    @8
    @3
    cT
    nmlnopne0
    biimpar
    sylan
    adantlr
    @7
    @8
    wa
    #
    @5
    @4
    @1
    chio
    chot
    co
    #
    chot
    co
    #
    chio
    cleo
    @10
    @4
    cr
    wcel
    #
    @0
    @11
    cho
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    cT
    @11
    cleo
    wbr
    #
    @5
    @12
    cleo
    wbr
    @2
    @8
    @13
    @0
    @1
    rereccl
    #
    adantll
    @0
    @2
    @8
    simpll
    @2
    @14
    @0
    @8
    @2
    chio
    cho
    wcel
    @14
    idhmop
    @1
    chio
    hmopm
    mpan2
    ad2antlr
    @10
    cc0
    @4
    clt
    wbr
    #
    @15
    @10
    @1
    @0
    @2
    @8
    simplr
    @0
    @8
    cc0
    @1
    clt
    wbr
    #
    @2
    @0
    chil
    chil
    cT
    wf
    #
    @8
    @19
    cT
    hmopf
    @20
    @8
    @19
    cT
    nmopgt0
    biimpa
    sylan
    adantlr
    recgt0d
    @2
    @8
    @18
    @15
    wi
    #
    @0
    @2
    @8
    wa
    cc0
    cr
    wcel
    @13
    @21
    0re
    @17
    cc0
    @4
    ltle
    sylancr
    adantll
    mpd
    @7
    @16
    @8
    cT
    leopnmid
    adantr
    @4
    cT
    @11
    leopmul2i
    syl32anc
    @2
    @8
    @12
    chio
    wceq
    #
    @0
    @2
    @1
    cc
    wcel
    #
    @8
    @22
    @1
    recn
    @23
    @8
    wa
    #
    @12
    c1
    chio
    chot
    co
    #
    chio
    @24
    @4
    @1
    cmul
    co
    #
    chio
    chot
    co
    #
    @12
    @25
    @24
    @4
    cc
    wcel
    #
    @23
    @27
    @12
    wceq
    #
    @1
    reccl
    @23
    @8
    simpl
    @28
    @23
    chil
    chil
    chio
    wf
    #
    @29
    chil
    chil
    chio
    wf1o
    @30
    hoif
    chil
    chil
    chio
    f1of
    ax-mp
    #
    @4
    @1
    chio
    homulass
    mp3an3
    syl2anc
    @24
    @26
    c1
    chio
    chot
    @1
    recid2
    oveq1d
    eqtr3d
    @30
    @25
    chio
    wceq
    @31
    chio
    homulid2
    ax-mp
    syl6eq
    sylan
    adantll
    breqtrd
    syldan
    3impa
end
