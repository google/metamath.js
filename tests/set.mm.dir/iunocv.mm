include "ciun.mm"
include "cfv.mm"
include "ciin.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "cip.mm"
include "co.mm"
include "csca.mm"
include "c0g.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "iunss.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "eliun.mm"
include "imbi1i.mm"
include "r19.23v.mm"
include "bitr4i.mm"
include "albii.mm"
include "df-ral.mm"
include "ralbii.mm"
include "ralcom4.mm"
include "bitri.mm"
include "3bitr4i.mm"
include "anbi12i.mm"
include "r19.26.mm"
include "eliin.mm"
include "w3a.mm"
include "eqid.mm"
include "elocv.mm"
include "3anan12.mm"
include "baib.mm"
include "ralbidv.mm"
include "bitr2d.mm"
include "syl5bb.mm"
include "pm5.32i.mm"
include "elin.mm"
include "eqriv.mm"

theorem iunocv
  let vx: setvar x
  let cA: class A
  let cB: class B
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vz: setvar z
  assume inocv.o: |- ._|_ = ( ocv ` W )
  assume iunocv.v: |- V = ( Base ` W )

  disjoint V x
  disjoint W x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint ._|_ z
  disjoint x y
  disjoint x z
  disjoint V y
  disjoint V z
  disjoint W y
  assert |- ( ._|_ ` U_ x e. A B ) = ( V i^i |^|_ x e. A ( ._|_ ` B ) )

  proof
    vz
    vx
    cA
    cB
    ciun
    #
    c.pe
    cfv
    #
    cV
    vx
    cA
    cB
    c.pe
    cfv
    #
    ciin
    #
    cin
    #
    vz
    cv
    #
    cV
    wcel
    #
    @0
    cV
    wss
    #
    @5
    vy
    cv
    #
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
    @6
    @5
    @3
    wcel
    #
    wa
    @5
    @1
    wcel
    #
    @5
    @4
    wcel
    @6
    @14
    @16
    @14
    cB
    cV
    wss
    #
    @12
    vy
    cB
    wral
    #
    wa
    #
    vx
    cA
    wral
    #
    @6
    @16
    @14
    @18
    vx
    cA
    wral
    #
    @19
    vx
    cA
    wral
    #
    wa
    @21
    @7
    @22
    @13
    @23
    vx
    cA
    cB
    cV
    iunss
    @8
    @0
    wcel
    #
    @12
    wi
    #
    vy
    wal
    @8
    cB
    wcel
    #
    @12
    wi
    #
    vx
    cA
    wral
    #
    vy
    wal
    #
    @13
    @23
    @25
    @28
    vy
    @25
    @26
    vx
    cA
    wrex
    #
    @12
    wi
    @28
    @24
    @30
    @12
    vx
    @8
    cA
    cB
    eliun
    imbi1i
    @26
    @12
    vx
    cA
    r19.23v
    bitr4i
    albii
    @12
    vy
    @0
    df-ral
    @23
    @27
    vy
    wal
    #
    vx
    cA
    wral
    @29
    @19
    @31
    vx
    cA
    @12
    vy
    cB
    df-ral
    ralbii
    @27
    vx
    vy
    cA
    ralcom4
    bitri
    3bitr4i
    anbi12i
    @18
    @19
    vx
    cA
    r19.26
    bitr4i
    @6
    @16
    @5
    @2
    wcel
    #
    vx
    cA
    wral
    @21
    vx
    @5
    cA
    @2
    cV
    eliin
    @6
    @32
    @20
    vx
    cA
    @32
    @6
    @20
    @32
    @18
    @6
    @19
    w3a
    @6
    @20
    wa
    vy
    @5
    cB
    @10
    @9
    c.pe
    cV
    cW
    @11
    iunocv.v
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
    @18
    @6
    @19
    3anan12
    bitri
    baib
    ralbidv
    bitr2d
    syl5bb
    pm5.32i
    @17
    @7
    @6
    @13
    w3a
    @15
    vy
    @5
    @0
    @10
    @9
    c.pe
    cV
    cW
    @11
    iunocv.v
    @33
    @34
    @35
    inocv.o
    elocv
    @7
    @6
    @13
    3anan12
    bitri
    @5
    cV
    @3
    elin
    3bitr4i
    eqriv
end
