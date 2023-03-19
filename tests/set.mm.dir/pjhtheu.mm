include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "cfv.mm"
include "wrex.mm"
include "wmo.mm"
include "wreu.mm"
include "cph.mm"
include "pjhth.mm"
include "eleq2d.mm"
include "csh.mm"
include "wb.mm"
include "chsh.mm"
include "shocsh.mm"
include "syl.mm"
include "shsel.mm"
include "syl2anc.mm"
include "bitr3d.mm"
include "biimpa.mm"
include "cin.mm"
include "c0h.mm"
include "ocin.mm"
include "pjhthmo.mm"
include "syl3anc.mm"
include "adantr.mm"
include "wrmo.mm"
include "reu5.mm"
include "df-rmo.mm"
include "anbi2i.mm"
include "bitri.mm"
include "sylanbrc.mm"

theorem pjhtheu
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cH: class H

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint H x
  disjoint H y
  assert |- ( ( H e. CH /\ A e. ~H ) -> E! x e. H E. y e. ( _|_ ` H ) A = ( x +h y ) )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    wa
    cA
    vx
    cv
    #
    vy
    cv
    cva
    co
    wceq
    vy
    cH
    cort
    cfv
    #
    wrex
    #
    vx
    cH
    wrex
    #
    @2
    cH
    wcel
    @4
    wa
    vx
    wmo
    #
    @4
    vx
    cH
    wreu
    #
    @0
    @1
    @5
    @0
    cA
    cH
    @3
    cph
    co
    #
    wcel
    #
    @1
    @5
    @0
    @8
    chil
    cA
    cH
    pjhth
    eleq2d
    @0
    cH
    csh
    wcel
    #
    @3
    csh
    wcel
    #
    @9
    @5
    wb
    cH
    chsh
    #
    @0
    @10
    @11
    @12
    cH
    shocsh
    syl
    #
    vx
    vy
    cH
    @3
    cA
    shsel
    syl2anc
    bitr3d
    biimpa
    @0
    @6
    @1
    @0
    @10
    @11
    cH
    @3
    cin
    c0h
    wceq
    #
    @6
    @12
    @13
    @0
    @10
    @14
    @12
    cH
    ocin
    syl
    vx
    vy
    cH
    @3
    cA
    pjhthmo
    syl3anc
    adantr
    @7
    @5
    @4
    vx
    cH
    wrmo
    #
    wa
    @5
    @6
    wa
    @4
    vx
    cH
    reu5
    @15
    @6
    @5
    @4
    vx
    cH
    df-rmo
    anbi2i
    bitri
    sylanbrc
end
