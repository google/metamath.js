include "cn.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "w3a.mm"
include "cmu.mm"
include "cfv.mm"
include "cc0.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cprime.mm"
include "wrex.mm"
include "wceq.mm"
include "wa.mm"
include "simpl3.mm"
include "cz.mm"
include "wi.mm"
include "prmz.mm"
include "adantl.mm"
include "zsqcl.mm"
include "syl.mm"
include "simpl2.mm"
include "nnzd.mm"
include "simpl1.mm"
include "dvdstr.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "reximdva.mm"
include "wb.mm"
include "isnsqf.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "3imtr4d.mm"
include "necon3d.mm"

theorem dvdssqf
  let cA: class A
  let cB: class B
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
  let cP: class P


  assert |- ( ( A e. NN /\ B e. NN /\ B || A ) -> ( ( mmu ` A ) =/= 0 -> ( mmu ` B ) =/= 0 ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cB
    cA
    cdvds
    wbr
    #
    w3a
    #
    cB
    cmu
    cfv
    #
    cc0
    cA
    cmu
    cfv
    #
    cc0
    @3
    vp
    cv
    #
    c2
    cexp
    co
    #
    cB
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    @7
    cA
    cdvds
    wbr
    #
    vp
    cprime
    wrex
    #
    @4
    cc0
    wceq
    #
    @5
    cc0
    wceq
    #
    @3
    @8
    @10
    vp
    cprime
    @3
    @6
    cprime
    wcel
    #
    wa
    #
    @8
    @2
    @10
    @0
    @1
    @2
    @14
    simpl3
    @15
    @7
    cz
    wcel
    #
    cB
    cz
    wcel
    cA
    cz
    wcel
    @8
    @2
    wa
    @10
    wi
    @15
    @6
    cz
    wcel
    #
    @16
    @14
    @17
    @3
    @6
    prmz
    adantl
    @6
    zsqcl
    syl
    @15
    cB
    @0
    @1
    @2
    @14
    simpl2
    nnzd
    @15
    cA
    @0
    @1
    @2
    @14
    simpl1
    nnzd
    @7
    cB
    cA
    dvdstr
    syl3anc
    mpan2d
    reximdva
    @1
    @0
    @12
    @9
    wb
    @2
    cB
    vp
    isnsqf
    3ad2ant2
    @0
    @1
    @13
    @11
    wb
    @2
    cA
    vp
    isnsqf
    3ad2ant1
    3imtr4d
    necon3d
end
