include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "csu.mm"
include "ccht.mm"
include "cfn.mm"
include "simp2.mm"
include "ppifi.mm"
include "syl.mm"
include "wa.mm"
include "cn.mm"
include "c1.mm"
include "clt.mm"
include "c2.mm"
include "cuz.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "prmuz2.mm"
include "eluz2b2.mm"
include "sylib.mm"
include "simpld.mm"
include "nnred.mm"
include "simprd.mm"
include "rplogcld.mm"
include "rpred.mm"
include "rpge0d.mm"
include "wss.mm"
include "0red.mm"
include "0le0.mm"
include "a1i.mm"
include "simp3.mm"
include "iccss.mm"
include "syl22anc.mm"
include "ssrin.mm"
include "fsumless.mm"
include "wceq.mm"
include "chtval.mm"
include "3ad2ant1.mm"
include "3brtr4d.mm"

theorem chtwordi
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


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( theta ` A ) <_ ( theta ` B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    #
    cc0
    cA
    cicc
    co
    #
    cprime
    cin
    #
    vp
    cv
    #
    clog
    cfv
    #
    vp
    csu
    #
    cc0
    cB
    cicc
    co
    #
    cprime
    cin
    #
    @7
    vp
    csu
    #
    cA
    ccht
    cfv
    #
    cB
    ccht
    cfv
    #
    cle
    @3
    @10
    @7
    @5
    vp
    @3
    @1
    @10
    cfn
    wcel
    @0
    @1
    @2
    simp2
    #
    cB
    ppifi
    syl
    @3
    @6
    @10
    wcel
    #
    wa
    #
    @7
    @16
    @6
    @16
    @6
    @16
    @6
    cn
    wcel
    #
    c1
    @6
    clt
    wbr
    #
    @16
    @6
    c2
    cuz
    cfv
    wcel
    #
    @17
    @18
    wa
    @16
    @6
    cprime
    wcel
    @19
    @16
    @10
    cprime
    @6
    @9
    cprime
    inss2
    @3
    @15
    simpr
    sseldi
    @6
    prmuz2
    syl
    @6
    eluz2b2
    sylib
    #
    simpld
    nnred
    @16
    @17
    @18
    @20
    simprd
    rplogcld
    #
    rpred
    @16
    @7
    @21
    rpge0d
    @3
    @4
    @9
    wss
    #
    @5
    @10
    wss
    @3
    cc0
    cr
    wcel
    @1
    cc0
    cc0
    cle
    wbr
    #
    @2
    @22
    @3
    0red
    @14
    @23
    @3
    0le0
    a1i
    @0
    @1
    @2
    simp3
    cc0
    cB
    cc0
    cA
    iccss
    syl22anc
    @4
    @9
    cprime
    ssrin
    syl
    fsumless
    @0
    @1
    @12
    @8
    wceq
    @2
    cA
    vp
    chtval
    3ad2ant1
    @3
    @1
    @13
    @11
    wceq
    @14
    cB
    vp
    chtval
    syl
    3brtr4d
end
