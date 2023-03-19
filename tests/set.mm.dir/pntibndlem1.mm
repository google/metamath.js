include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cioo.mm"
include "co.mm"
include "c4.mm"
include "cdiv.mm"
include "c3.mm"
include "caddc.mm"
include "crp.mm"
include "cn.mm"
include "4nn.mm"
include "nnrp.mm"
include "rpreccl.mm"
include "mp2b.mm"
include "3nn.mm"
include "ax-mp.mm"
include "rpaddcl.mm"
include "sylancl.mm"
include "rpdivcl.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "rpred.mm"
include "rpgt0d.mm"
include "cc.mm"
include "rpcn.mm"
include "div1i.mm"
include "rpre.mm"
include "mp1i.mm"
include "3re.mm"
include "a1i.mm"
include "1lt4.mm"
include "wb.mm"
include "4re.mm"
include "4pos.mm"
include "recgt1.mm"
include "mp2an.mm"
include "mpbi.mm"
include "1lt3.mm"
include "1re.mm"
include "lttri.mm"
include "ltaddrp.mm"
include "wceq.mm"
include "3cn.mm"
include "rpcnd.mm"
include "addcom.mm"
include "breqtrd.mm"
include "lttrd.mm"
include "syl5eqbr.mm"
include "wa.mm"
include "0lt1.mm"
include "rpregt0d.mm"
include "ltdiv23.mm"
include "syl121anc.mm"
include "mpbid.mm"
include "cxr.mm"
include "w3a.mm"
include "0xr.mm"
include "rexri.mm"
include "elioo2.mm"
include "syl3anbrc.mm"

theorem pntibndlem1
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cL: class L
  let va: setvar a
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cE: class E
  let cN: class N
  let cC: class C
  let vc: setvar c
  let ve: setvar e
  let cK: class K
  let cM: class M
  let cT: class T
  let cY: class Y
  let cZ: class Z
  assume pntibnd.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )
  assume pntibndlem1.1: |- ( ph -> A e. RR+ )
  assume pntibndlem1.l: |- L = ( ( 1 / 4 ) / ( A + 3 ) )


  assert |- ( ph -> L e. ( 0 (,) 1 ) )

  proof
    wph
    cL
    cr
    wcel
    #
    cc0
    cL
    clt
    wbr
    #
    cL
    c1
    clt
    wbr
    #
    cL
    cc0
    c1
    cioo
    co
    wcel
    #
    wph
    cL
    wph
    cL
    c1
    c4
    cdiv
    co
    #
    cA
    c3
    caddc
    co
    #
    cdiv
    co
    #
    crp
    pntibndlem1.l
    wph
    @4
    crp
    wcel
    #
    @5
    crp
    wcel
    #
    @6
    crp
    wcel
    c4
    cn
    wcel
    c4
    crp
    wcel
    @7
    4nn
    c4
    nnrp
    c4
    rpreccl
    mp2b
    #
    wph
    cA
    crp
    wcel
    #
    c3
    crp
    wcel
    #
    @8
    pntibndlem1.1
    c3
    cn
    wcel
    @11
    3nn
    c3
    nnrp
    ax-mp
    cA
    c3
    rpaddcl
    sylancl
    #
    @4
    @5
    rpdivcl
    sylancr
    syl5eqel
    #
    rpred
    wph
    cL
    @13
    rpgt0d
    wph
    cL
    @6
    c1
    clt
    pntibndlem1.l
    wph
    @4
    c1
    cdiv
    co
    #
    @5
    clt
    wbr
    #
    @6
    c1
    clt
    wbr
    #
    wph
    @14
    @4
    @5
    clt
    @4
    @7
    @4
    cc
    wcel
    @9
    @4
    rpcn
    ax-mp
    div1i
    wph
    @4
    c3
    @5
    @7
    @4
    cr
    wcel
    #
    wph
    @9
    @4
    rpre
    #
    mp1i
    #
    c3
    cr
    wcel
    #
    wph
    3re
    a1i
    wph
    @5
    @12
    rpred
    @4
    c3
    clt
    wbr
    #
    wph
    @4
    c1
    clt
    wbr
    #
    c1
    c3
    clt
    wbr
    @21
    c1
    c4
    clt
    wbr
    #
    @22
    1lt4
    c4
    cr
    wcel
    cc0
    c4
    clt
    wbr
    @23
    @22
    wb
    4re
    4pos
    c4
    recgt1
    mp2an
    mpbi
    1lt3
    @4
    c1
    c3
    @7
    @17
    @9
    @18
    ax-mp
    1re
    3re
    lttri
    mp2an
    a1i
    wph
    c3
    c3
    cA
    caddc
    co
    #
    @5
    clt
    wph
    @20
    @10
    c3
    @24
    clt
    wbr
    3re
    pntibndlem1.1
    c3
    cA
    ltaddrp
    sylancr
    wph
    c3
    cc
    wcel
    cA
    cc
    wcel
    @24
    @5
    wceq
    3cn
    wph
    cA
    pntibndlem1.1
    rpcnd
    c3
    cA
    addcom
    sylancr
    breqtrd
    lttrd
    syl5eqbr
    wph
    @17
    c1
    cr
    wcel
    #
    cc0
    c1
    clt
    wbr
    #
    @5
    cr
    wcel
    cc0
    @5
    clt
    wbr
    wa
    @15
    @16
    wb
    @19
    @25
    wph
    1re
    a1i
    @26
    wph
    0lt1
    a1i
    wph
    @5
    @12
    rpregt0d
    @4
    c1
    @5
    ltdiv23
    syl121anc
    mpbid
    syl5eqbr
    cc0
    cxr
    wcel
    c1
    cxr
    wcel
    @3
    @0
    @1
    @2
    w3a
    wb
    0xr
    c1
    1re
    rexri
    cc0
    c1
    cL
    elioo2
    mp2an
    syl3anbrc
end
