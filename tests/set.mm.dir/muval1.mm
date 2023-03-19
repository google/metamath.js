include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "w3a.mm"
include "cmu.mm"
include "cv.mm"
include "cprime.mm"
include "wrex.mm"
include "cc0.mm"
include "c1.mm"
include "cneg.mm"
include "crab.mm"
include "chash.mm"
include "cif.mm"
include "wceq.mm"
include "muval.mm"
include "3ad2ant1.mm"
include "exprmfct.mm"
include "3ad2ant2.mm"
include "wa.mm"
include "wb.mm"
include "prmnn.mm"
include "adantl.mm"
include "clt.mm"
include "simpl2.mm"
include "eluz2b2.mm"
include "sylib.mm"
include "simpld.mm"
include "dvdssqlem.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "cz.mm"
include "wi.mm"
include "prmz.mm"
include "zsqcl.mm"
include "syl.mm"
include "eluzelz.mm"
include "3syl.mm"
include "simpl1.mm"
include "nnzd.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "sylbid.mm"
include "reximdva.mm"
include "mpd.mm"
include "iftrued.mm"
include "eqtrd.mm"

theorem muval1
  let cA: class A
  let cP: class P
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B


  assert |- ( ( A e. NN /\ P e. ( ZZ>= ` 2 ) /\ ( P ^ 2 ) || A ) -> ( mmu ` A ) = 0 )

  proof
    cA
    cn
    wcel
    #
    cP
    c2
    cuz
    cfv
    wcel
    #
    cP
    c2
    cexp
    co
    #
    cA
    cdvds
    wbr
    #
    w3a
    #
    cA
    cmu
    cfv
    #
    vp
    cv
    #
    c2
    cexp
    co
    #
    cA
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    cc0
    c1
    cneg
    @6
    cA
    cdvds
    wbr
    vp
    cprime
    crab
    chash
    cfv
    cexp
    co
    #
    cif
    #
    cc0
    @0
    @1
    @5
    @11
    wceq
    @3
    cA
    vp
    muval
    3ad2ant1
    @4
    @9
    cc0
    @10
    @4
    @6
    cP
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    @9
    @1
    @0
    @13
    @3
    cP
    vp
    exprmfct
    3ad2ant2
    @4
    @12
    @8
    vp
    cprime
    @4
    @6
    cprime
    wcel
    #
    wa
    #
    @12
    @7
    @2
    cdvds
    wbr
    #
    @8
    @15
    @6
    cn
    wcel
    #
    cP
    cn
    wcel
    #
    @12
    @16
    wb
    @14
    @17
    @4
    @6
    prmnn
    adantl
    @15
    @18
    c1
    cP
    clt
    wbr
    #
    @15
    @1
    @18
    @19
    wa
    @0
    @1
    @3
    @14
    simpl2
    #
    cP
    eluz2b2
    sylib
    simpld
    @6
    cP
    dvdssqlem
    syl2anc
    @15
    @16
    @3
    @8
    @0
    @1
    @3
    @14
    simpl3
    @15
    @7
    cz
    wcel
    #
    @2
    cz
    wcel
    #
    cA
    cz
    wcel
    @16
    @3
    wa
    @8
    wi
    @15
    @6
    cz
    wcel
    #
    @21
    @14
    @23
    @4
    @6
    prmz
    adantl
    @6
    zsqcl
    syl
    @15
    @1
    cP
    cz
    wcel
    @22
    @20
    c2
    cP
    eluzelz
    cP
    zsqcl
    3syl
    @15
    cA
    @0
    @1
    @3
    @14
    simpl1
    nnzd
    @7
    @2
    cA
    dvdstr
    syl3anc
    mpan2d
    sylbid
    reximdva
    mpd
    iftrued
    eqtrd
end
