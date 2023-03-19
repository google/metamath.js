include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wne.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "eldifsn.mm"
include "cz.mm"
include "c2.mm"
include "wceq.mm"
include "wrex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "zcn.mm"
include "adantr.mm"
include "sylbi.mm"
include "anim1i.mm"
include "ancli.mm"
include "cdiv.mm"
include "c1.mm"
include "wnel.mm"
include "1neven.mm"
include "elnelne2.mm"
include "mpan2.mm"
include "ad2antrl.mm"
include "w3a.mm"
include "simpr.mm"
include "anim2i.mm"
include "3anass.mm"
include "ancom.mm"
include "bitri.mm"
include "sylibr.mm"
include "divcan3.mm"
include "syl.mm"
include "divid.mm"
include "3netr4d.mm"
include "wb.mm"
include "simpl.mm"
include "mulcl.mm"
include "syl2an.mm"
include "div11.mm"
include "syl3anc.mm"
include "biimprd.mm"
include "necon3d.mm"
include "mpd.mm"
include "rgen2.mm"

theorem 2zrngnmrid
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cE: class E
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vk: setvar k
  assume 2zrng.e: |- E = { z e. ZZ | E. x e. ZZ z = ( 2 x. x ) }
  assume 2zrngbas.r: |- R = ( CCfld |`s E )
  assume 2zrngmmgm.1: |- M = ( mulGrp ` R )

  disjoint x z
  disjoint E a
  disjoint E b
  disjoint a b
  disjoint R a
  disjoint R b
  disjoint a x
  disjoint a z
  disjoint b x
  disjoint b z
  disjoint R x
  disjoint R z
  disjoint E x
  disjoint E z
  disjoint M a
  disjoint M b
  disjoint a y
  disjoint b y
  disjoint x y
  disjoint y z
  disjoint R y
  disjoint E y
  disjoint M y
  disjoint k x
  assert |- A. a e. ( E \ { 0 } ) A. b e. E ( a x. b ) =/= a

  proof
    va
    cv
    #
    vb
    cv
    #
    cmul
    co
    #
    @0
    wne
    #
    va
    vb
    cE
    cc0
    csn
    cdif
    #
    cE
    @0
    @4
    wcel
    #
    @0
    cc
    wcel
    #
    @0
    cc0
    wne
    #
    wa
    #
    @1
    cE
    wcel
    #
    @1
    cc
    wcel
    #
    wa
    #
    @3
    @9
    @5
    @0
    cE
    wcel
    #
    @7
    wa
    @8
    @0
    cE
    cc0
    eldifsn
    @12
    @6
    @7
    @12
    @0
    cz
    wcel
    #
    @0
    c2
    vx
    cv
    cmul
    co
    #
    wceq
    #
    vx
    cz
    wrex
    #
    wa
    @6
    vz
    cv
    #
    @14
    wceq
    #
    vx
    cz
    wrex
    #
    @16
    vz
    @0
    cz
    cE
    @17
    @0
    wceq
    @18
    @15
    vx
    cz
    @17
    @0
    @14
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    @13
    @6
    @16
    @0
    zcn
    adantr
    sylbi
    anim1i
    sylbi
    @9
    @10
    @9
    @1
    cz
    wcel
    #
    @1
    @14
    wceq
    #
    vx
    cz
    wrex
    #
    wa
    @10
    @19
    @22
    vz
    @1
    cz
    cE
    @17
    @1
    wceq
    @18
    @21
    vx
    cz
    @17
    @1
    @14
    eqeq1
    rexbidv
    2zrng.e
    elrab2
    @20
    @10
    @22
    @1
    zcn
    adantr
    sylbi
    ancli
    @8
    @11
    wa
    #
    @2
    @0
    cdiv
    co
    #
    @0
    @0
    cdiv
    co
    #
    wne
    @3
    @23
    @1
    c1
    @24
    @25
    @9
    @1
    c1
    wne
    #
    @8
    @10
    @9
    c1
    cE
    wnel
    @26
    vx
    vz
    cE
    2zrng.e
    1neven
    @1
    c1
    cE
    elnelne2
    mpan2
    ad2antrl
    @23
    @10
    @6
    @7
    w3a
    #
    @24
    @1
    wceq
    @23
    @8
    @10
    wa
    #
    @27
    @11
    @10
    @8
    @9
    @10
    simpr
    #
    anim2i
    @27
    @10
    @8
    wa
    @28
    @10
    @6
    @7
    3anass
    @10
    @8
    ancom
    bitri
    sylibr
    @1
    @0
    divcan3
    syl
    @8
    @25
    c1
    wceq
    @11
    @0
    divid
    adantr
    3netr4d
    @23
    @2
    @0
    @24
    @25
    @23
    @24
    @25
    wceq
    #
    @2
    @0
    wceq
    #
    @23
    @2
    cc
    wcel
    #
    @6
    @8
    @30
    @31
    wb
    @8
    @6
    @10
    @32
    @11
    @6
    @7
    simpl
    #
    @29
    @0
    @1
    mulcl
    syl2an
    @8
    @6
    @11
    @33
    adantr
    @8
    @11
    simpl
    @2
    @0
    @0
    div11
    syl3anc
    biimprd
    necon3d
    mpd
    syl2an
    rgen2
end
