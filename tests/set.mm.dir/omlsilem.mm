include "cva.mm"
include "co.mm"
include "wceq.mm"
include "wcel.mm"
include "c0v.mm"
include "cort.mm"
include "cfv.mm"
include "cmv.mm"
include "shelii.mm"
include "chil.mm"
include "csh.mm"
include "wss.mm"
include "shocss.mm"
include "ax-mp.mm"
include "sselii.mm"
include "hvsubaddi.mm"
include "eqcom.mm"
include "bitri.mm"
include "shsubcl.mm"
include "mp3an.mm"
include "eleq1.mm"
include "mpbii.mm"
include "sylbir.mm"
include "cin.mm"
include "c0h.mm"
include "wa.mm"
include "eleq2i.mm"
include "elin.mm"
include "elch0.mm"
include "3bitr3i.mm"
include "sylanblc.mm"
include "oveq2d.mm"
include "ax-hvaddid.mm"
include "syl6eq.mm"
include "syl6eqel.mm"
include "mpbird.mm"

theorem omlsilem
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let cH: class H
  assume omlsilem.1: |- G e. SH
  assume omlsilem.2: |- H e. SH
  assume omlsilem.3: |- G C_ H
  assume omlsilem.4: |- ( H i^i ( _|_ ` G ) ) = 0H
  assume omlsilem.5: |- A e. H
  assume omlsilem.6: |- B e. G
  assume omlsilem.7: |- C e. ( _|_ ` G )


  assert |- ( A = ( B +h C ) -> A e. G )

  proof
    cA
    cB
    cC
    cva
    co
    #
    wceq
    #
    cA
    cG
    wcel
    @0
    cG
    wcel
    @1
    @0
    cB
    cG
    @1
    @0
    cB
    c0v
    cva
    co
    #
    cB
    @1
    cC
    c0v
    cB
    cva
    @1
    cC
    cH
    wcel
    #
    cC
    cG
    cort
    cfv
    #
    wcel
    #
    cC
    c0v
    wceq
    #
    @1
    cA
    cB
    cmv
    co
    #
    cC
    wceq
    #
    @3
    @8
    @0
    cA
    wceq
    @1
    cA
    cB
    cC
    cA
    cH
    omlsilem.2
    omlsilem.5
    shelii
    cB
    cG
    omlsilem.1
    omlsilem.6
    shelii
    #
    @4
    chil
    cC
    cG
    csh
    wcel
    @4
    chil
    wss
    omlsilem.1
    cG
    shocss
    ax-mp
    omlsilem.7
    sselii
    hvsubaddi
    @0
    cA
    eqcom
    bitri
    @8
    @7
    cH
    wcel
    #
    @3
    cH
    csh
    wcel
    cA
    cH
    wcel
    cB
    cH
    wcel
    @10
    omlsilem.2
    omlsilem.5
    cG
    cH
    cB
    omlsilem.3
    omlsilem.6
    sselii
    cA
    cB
    cH
    shsubcl
    mp3an
    @7
    cC
    cH
    eleq1
    mpbii
    sylbir
    omlsilem.7
    cC
    cH
    @4
    cin
    #
    wcel
    cC
    c0h
    wcel
    @3
    @5
    wa
    @6
    @11
    c0h
    cC
    omlsilem.4
    eleq2i
    cC
    cH
    @4
    elin
    cC
    elch0
    3bitr3i
    sylanblc
    oveq2d
    cB
    chil
    wcel
    @2
    cB
    wceq
    @9
    cB
    ax-hvaddid
    ax-mp
    syl6eq
    omlsilem.6
    syl6eqel
    cA
    @0
    cG
    eleq1
    mpbird
end
