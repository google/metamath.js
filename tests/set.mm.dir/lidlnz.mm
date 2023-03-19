include "crg.mm"
include "wcel.mm"
include "csn.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wn.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "wpss.mm"
include "wss.mm"
include "lidl0cl.mm"
include "snssd.mm"
include "3adant3.mm"
include "simp3.mm"
include "necomd.mm"
include "df-pss.mm"
include "sylanbrc.mm"
include "pssnel.mm"
include "syl.mm"
include "velsn.mm"
include "necon3bbii.mm"
include "anbi2i.mm"
include "exbii.mm"
include "df-rex.mm"
include "bitr4i.mm"
include "sylib.mm"

theorem lidlnz
  let vx: setvar x
  let cR: class R
  let cU: class U
  let cI: class I
  let c.0: class .0.
  assume lidlnz.u: |- U = ( LIdeal ` R )
  assume lidlnz.z: |- .0. = ( 0g ` R )

  disjoint I x
  disjoint .0. x
  assert |- ( ( R e. Ring /\ I e. U /\ I =/= { .0. } ) -> E. x e. I x =/= .0. )

  proof
    cR
    crg
    wcel
    #
    cI
    cU
    wcel
    #
    cI
    c.0
    csn
    #
    wne
    #
    w3a
    #
    vx
    cv
    #
    cI
    wcel
    #
    @5
    @2
    wcel
    #
    wn
    #
    wa
    #
    vx
    wex
    #
    @5
    c.0
    wne
    #
    vx
    cI
    wrex
    #
    @4
    @2
    cI
    wpss
    #
    @10
    @4
    @2
    cI
    wss
    #
    @2
    cI
    wne
    @13
    @0
    @1
    @14
    @3
    @0
    @1
    wa
    c.0
    cI
    cR
    cU
    cI
    c.0
    lidlnz.u
    lidlnz.z
    lidl0cl
    snssd
    3adant3
    @4
    cI
    @2
    @0
    @1
    @3
    simp3
    necomd
    @2
    cI
    df-pss
    sylanbrc
    vx
    @2
    cI
    pssnel
    syl
    @10
    @6
    @11
    wa
    #
    vx
    wex
    @12
    @9
    @15
    vx
    @8
    @11
    @6
    @7
    @5
    c.0
    vx
    c.0
    velsn
    necon3bbii
    anbi2i
    exbii
    @11
    vx
    cI
    df-rex
    bitr4i
    sylib
end
