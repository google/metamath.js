include "wfun.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wfrrel.mm"
include "wfn.mm"
include "wss.mm"
include "cpred.mm"
include "wral.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "cab.mm"
include "wcel.mm"
include "cop.mm"
include "cuni.mm"
include "cwrecs.mm"
include "df-wrecs.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "eluni.mm"
include "bitri.mm"
include "df-br.mm"
include "anbi1i.mm"
include "exbii.mm"
include "3bitr4i.mm"
include "anbi12i.mm"
include "eeanv.mm"
include "bitr4i.mm"
include "eqid.mm"
include "wfrlem5.mm"
include "impcom.mm"
include "an4s.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "ax-gen.mm"
include "gen2.mm"
include "dffun2.mm"
include "mpbir2an.mm"

theorem wfrfun
  let cA: class A
  let cR: class R
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wfrfun.1: |- R We A
  assume wfrfun.2: |- R Se A
  assume wfrfun.3: |- F = wrecs ( R , A , G )


  assert |- Fun F

  proof
    cF
    wfun
    cF
    wrel
    vx
    cv
    #
    vu
    cv
    #
    cF
    wbr
    #
    @0
    vv
    cv
    #
    cF
    wbr
    #
    wa
    #
    vu
    vv
    weq
    #
    wi
    #
    vv
    wal
    #
    vu
    wal
    vx
    wal
    cA
    cR
    cF
    cG
    wfrfun.3
    wfrrel
    @8
    vx
    vu
    @7
    vv
    @5
    @0
    @1
    vg
    cv
    #
    wbr
    #
    @9
    vf
    cv
    #
    @0
    wfn
    @0
    cA
    wss
    cA
    cR
    vy
    cv
    #
    cpred
    #
    @0
    wss
    vy
    @0
    wral
    wa
    @12
    @11
    cfv
    @11
    @13
    cres
    cG
    cfv
    wceq
    vy
    @0
    wral
    w3a
    vx
    wex
    vf
    cab
    #
    wcel
    #
    wa
    #
    @0
    @3
    vh
    cv
    #
    wbr
    #
    @17
    @14
    wcel
    #
    wa
    #
    wa
    #
    vh
    wex
    vg
    wex
    #
    @6
    @5
    @16
    vg
    wex
    #
    @20
    vh
    wex
    #
    wa
    @22
    @2
    @23
    @4
    @24
    @0
    @1
    cop
    #
    cF
    wcel
    #
    @25
    @9
    wcel
    #
    @15
    wa
    #
    vg
    wex
    #
    @2
    @23
    @26
    @25
    @14
    cuni
    #
    wcel
    @29
    cF
    @30
    @25
    cF
    cA
    cR
    cG
    cwrecs
    @30
    wfrfun.3
    vx
    vy
    cA
    cR
    vf
    cG
    df-wrecs
    eqtri
    #
    eleq2i
    vg
    @25
    @14
    eluni
    bitri
    @0
    @1
    cF
    df-br
    @16
    @28
    vg
    @10
    @27
    @15
    @0
    @1
    @9
    df-br
    anbi1i
    exbii
    3bitr4i
    @0
    @3
    cop
    #
    cF
    wcel
    #
    @32
    @17
    wcel
    #
    @19
    wa
    #
    vh
    wex
    #
    @4
    @24
    @33
    @32
    @30
    wcel
    @36
    cF
    @30
    @32
    @31
    eleq2i
    vh
    @32
    @14
    eluni
    bitri
    @0
    @3
    cF
    df-br
    @20
    @35
    vh
    @18
    @34
    @19
    @0
    @3
    @17
    df-br
    anbi1i
    exbii
    3bitr4i
    anbi12i
    @16
    @20
    vg
    vh
    eeanv
    bitr4i
    @21
    @6
    vg
    vh
    @10
    @18
    @15
    @19
    @6
    @15
    @19
    wa
    @10
    @18
    wa
    @6
    vx
    vy
    vv
    vu
    cA
    @14
    cR
    vf
    vg
    vh
    cG
    wfrfun.1
    wfrfun.2
    @14
    eqid
    wfrlem5
    impcom
    an4s
    exlimivv
    sylbi
    ax-gen
    gen2
    vx
    vu
    vv
    cF
    dffun2
    mpbir2an
end
