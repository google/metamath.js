include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cdiv.mm"
include "cmo.mm"
include "clt.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "wrex.mm"
include "cz.mm"
include "crab.mm"
include "chash.mm"
include "cfv.mm"
include "c4.mm"
include "cfl.mm"
include "caddc.mm"
include "2lgslem1a.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wf1o.mm"
include "wex.mm"
include "ovex.mm"
include "cmpt.mm"
include "mptex.mm"
include "f1oeq1.mm"
include "eqid.mm"
include "2lgslem1b.mm"
include "ceqsexv2d.mm"
include "a1i.mm"
include "hasheqf1oi.mm"
include "mpsyl.mm"
include "cuz.mm"
include "cle.mm"
include "prmz.mm"
include "zred.mm"
include "cr.mm"
include "4re.mm"
include "cc0.mm"
include "wne.mm"
include "4ne0.mm"
include "redivcld.mm"
include "flcld.mm"
include "adantr.mm"
include "wb.mm"
include "oddm1d2.mm"
include "syl.mm"
include "biimpa.mm"
include "2lgslem1c.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "hashfzp1.mm"
include "3eqtr2d.mm"

theorem 2lgslem1
  let vx: setvar x
  let cP: class P
  let vi: setvar i
  let vf: setvar f
  let vy: setvar y

  disjoint P i
  disjoint P x
  disjoint i x
  disjoint P f
  disjoint P y
  disjoint f i
  disjoint f x
  disjoint f y
  disjoint i y
  disjoint x y
  assert |- ( ( P e. Prime /\ -. 2 || P ) -> ( # ` { x e. ZZ | E. i e. ( 1 ... ( ( P - 1 ) / 2 ) ) ( x = ( i x. 2 ) /\ ( P / 2 ) < ( x mod P ) ) } ) = ( ( ( P - 1 ) / 2 ) - ( |_ ` ( P / 4 ) ) ) )

  proof
    cP
    cprime
    wcel
    #
    c2
    cP
    cdvds
    wbr
    wn
    #
    wa
    #
    vx
    cv
    #
    vi
    cv
    c2
    cmul
    co
    wceq
    #
    cP
    c2
    cdiv
    co
    @3
    cP
    cmo
    co
    clt
    wbr
    wa
    vi
    c1
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cfz
    co
    wrex
    vx
    cz
    crab
    #
    chash
    cfv
    @4
    vi
    cP
    c4
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    @5
    cfz
    co
    #
    wrex
    vx
    cz
    crab
    #
    chash
    cfv
    #
    @10
    chash
    cfv
    #
    @5
    @8
    cmin
    co
    #
    @2
    @6
    @11
    chash
    vx
    cP
    vi
    2lgslem1a
    fveq2d
    @10
    cvv
    wcel
    @2
    @10
    @11
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @13
    @12
    wceq
    @9
    @5
    cfz
    ovex
    #
    @17
    @2
    @16
    @10
    @11
    vy
    @10
    vy
    cv
    c2
    cmul
    co
    #
    cmpt
    #
    wf1o
    vf
    @20
    vy
    @10
    @19
    @18
    mptex
    @10
    @11
    @15
    @20
    f1oeq1
    vx
    @9
    @5
    vi
    vy
    @20
    @10
    @10
    eqid
    @20
    eqid
    2lgslem1b
    ceqsexv2d
    a1i
    @10
    @11
    vf
    cvv
    hasheqf1oi
    mpsyl
    @2
    @5
    @8
    cuz
    cfv
    wcel
    #
    @13
    @14
    wceq
    @2
    @8
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @8
    @5
    cle
    wbr
    @21
    @0
    @22
    @1
    @0
    @7
    @0
    cP
    c4
    @0
    cP
    cP
    prmz
    #
    zred
    c4
    cr
    wcel
    @0
    4re
    a1i
    c4
    cc0
    wne
    @0
    4ne0
    a1i
    redivcld
    flcld
    adantr
    @0
    @1
    @23
    @0
    cP
    cz
    wcel
    @1
    @23
    wb
    @24
    cP
    oddm1d2
    syl
    biimpa
    cP
    2lgslem1c
    @8
    @5
    eluz2
    syl3anbrc
    @8
    @5
    hashfzp1
    syl
    3eqtr2d
end
