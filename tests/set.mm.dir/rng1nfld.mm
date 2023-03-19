include "wcel.mm"
include "cfield.mm"
include "wn.mm"
include "wnel.mm"
include "cdr.mm"
include "cnzr.mm"
include "rng1nnzr.mm"
include "df-nel.mm"
include "sylib.mm"
include "drngnzr.mm"
include "nsyl.mm"
include "ccrg.mm"
include "wa.mm"
include "isfld.mm"
include "wi.mm"
include "simpl.mm"
include "a1i.mm"
include "syl5bi.mm"
include "mtod.mm"
include "sylibr.mm"

theorem rng1nfld
  let cM: class M
  let cV: class V
  let cZ: class Z
  assume rng1nfld.m: |- M = { <. ( Base ` ndx ) , { Z } >. , <. ( +g ` ndx ) , { <. <. Z , Z >. , Z >. } >. , <. ( .r ` ndx ) , { <. <. Z , Z >. , Z >. } >. }


  assert |- ( Z e. V -> M e/ Field )

  proof
    cZ
    cV
    wcel
    #
    cM
    cfield
    wcel
    #
    wn
    cM
    cfield
    wnel
    @0
    @1
    cM
    cdr
    wcel
    #
    @0
    cM
    cnzr
    wcel
    #
    @2
    @0
    cM
    cnzr
    wnel
    @3
    wn
    cM
    cV
    cZ
    rng1nfld.m
    rng1nnzr
    cM
    cnzr
    df-nel
    sylib
    cM
    drngnzr
    nsyl
    @1
    @2
    cM
    ccrg
    wcel
    #
    wa
    #
    @0
    @2
    cM
    isfld
    @5
    @2
    wi
    @0
    @2
    @4
    simpl
    a1i
    syl5bi
    mtod
    cM
    cfield
    df-nel
    sylibr
end
