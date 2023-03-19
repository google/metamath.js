include "cun.mm"
include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "cbs.mm"
include "wcel.mm"
include "wss.mm"
include "cip.mm"
include "co.mm"
include "csca.mm"
include "c0g.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "unss.mm"
include "bicomi.mm"
include "ralunb.mm"
include "anbi12i.mm"
include "an4.mm"
include "bitri.mm"
include "anbi2i.mm"
include "w3a.mm"
include "eqid.mm"
include "elocv.mm"
include "3anan12.mm"
include "elin.mm"
include "anandi.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem unocv
  let cA: class A
  let cB: class B
  let c.pe: class ._|_
  let cW: class W
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  let cV: class V
  assume inocv.o: |- ._|_ = ( ocv ` W )


  assert |- ( ._|_ ` ( A u. B ) ) = ( ( ._|_ ` A ) i^i ( ._|_ ` B ) )

  proof
    vz
    cA
    cB
    cun
    #
    c.pe
    cfv
    #
    cA
    c.pe
    cfv
    #
    cB
    c.pe
    cfv
    #
    cin
    #
    vz
    cv
    #
    cW
    cbs
    cfv
    #
    wcel
    #
    @0
    @6
    wss
    #
    @5
    vy
    cv
    cW
    cip
    cfv
    #
    co
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    vy
    @0
    wral
    #
    wa
    #
    wa
    #
    @7
    cA
    @6
    wss
    #
    @12
    vy
    cA
    wral
    #
    wa
    #
    cB
    @6
    wss
    #
    @12
    vy
    cB
    wral
    #
    wa
    #
    wa
    #
    wa
    #
    @5
    @1
    wcel
    #
    @5
    @4
    wcel
    #
    @14
    @22
    @7
    @14
    @16
    @19
    wa
    #
    @17
    @20
    wa
    #
    wa
    @22
    @8
    @26
    @13
    @27
    @26
    @8
    cA
    cB
    @6
    unss
    bicomi
    @12
    vy
    cA
    cB
    ralunb
    anbi12i
    @16
    @19
    @17
    @20
    an4
    bitri
    anbi2i
    @24
    @8
    @7
    @13
    w3a
    @15
    vy
    @5
    @0
    @10
    @9
    c.pe
    @6
    cW
    @11
    @6
    eqid
    #
    @9
    eqid
    #
    @10
    eqid
    #
    @11
    eqid
    #
    inocv.o
    elocv
    @8
    @7
    @13
    3anan12
    bitri
    @5
    @2
    wcel
    #
    @5
    @3
    wcel
    #
    wa
    @7
    @18
    wa
    #
    @7
    @21
    wa
    #
    wa
    @25
    @23
    @32
    @34
    @33
    @35
    @32
    @16
    @7
    @17
    w3a
    @34
    vy
    @5
    cA
    @10
    @9
    c.pe
    @6
    cW
    @11
    @28
    @29
    @30
    @31
    inocv.o
    elocv
    @16
    @7
    @17
    3anan12
    bitri
    @33
    @19
    @7
    @20
    w3a
    @35
    vy
    @5
    cB
    @10
    @9
    c.pe
    @6
    cW
    @11
    @28
    @29
    @30
    @31
    inocv.o
    elocv
    @19
    @7
    @20
    3anan12
    bitri
    anbi12i
    @5
    @2
    @3
    elin
    @7
    @18
    @21
    anandi
    3bitr4i
    3bitr4i
    eqriv
end
