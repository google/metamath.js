include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "ancom.mm"
include "cz.mm"
include "wb.mm"
include "prmz.mm"
include "rabeq2i.mm"
include "baib.mm"
include "syl.mm"
include "pm5.32i.mm"
include "bitr2i.mm"
include "nnoddn2prmb.mm"
include "elin.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem oddprm2
  let vz: setvar z
  let cO: class O
  assume hgt750leme.o: |- O = { z e. ZZ | -. 2 || z }

  disjoint O z
  assert |- ( Prime \ { 2 } ) = ( O i^i Prime )

  proof
    vz
    cprime
    c2
    csn
    cdif
    #
    cO
    cprime
    cin
    #
    vz
    cv
    #
    cprime
    wcel
    #
    c2
    @2
    cdvds
    wbr
    wn
    #
    wa
    #
    @2
    cO
    wcel
    #
    @3
    wa
    #
    @2
    @0
    wcel
    @2
    @1
    wcel
    @7
    @3
    @6
    wa
    @5
    @6
    @3
    ancom
    @3
    @6
    @4
    @3
    @2
    cz
    wcel
    #
    @6
    @4
    wb
    @2
    prmz
    @6
    @8
    @4
    @4
    vz
    cO
    cz
    hgt750leme.o
    rabeq2i
    baib
    syl
    pm5.32i
    bitr2i
    @2
    nnoddn2prmb
    @2
    cO
    cprime
    elin
    3bitr4i
    eqriv
end
