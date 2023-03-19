include "cdr.mm"
include "wcel.mm"
include "csn.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "cdif.mm"
include "cima.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "cin.mm"
include "crab.mm"
include "crio.mm"
include "cif.mm"
include "ig1pval.mm"
include "3adant3.mm"
include "simp3.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "wreu.mm"
include "ig1peu.mm"
include "riotacl2.mm"
include "syl.mm"
include "eqeltrd.mm"
include "wa.mm"
include "elin.mm"
include "anbi1i.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "df-3an.mm"
include "3bitr4i.mm"
include "sylib.mm"

theorem ig1pval3
  let cD: class D
  let cP: class P
  let cR: class R
  let cU: class U
  let cG: class G
  let cI: class I
  let cM: class M
  let c.0: class .0.
  let vg: setvar g
  assume ig1pval.p: |- P = ( Poly1 ` R )
  assume ig1pval.g: |- G = ( idlGen1p ` R )
  assume ig1pval3.z: |- .0. = ( 0g ` P )
  assume ig1pval3.u: |- U = ( LIdeal ` P )
  assume ig1pval3.d: |- D = ( deg1 ` R )
  assume ig1pval3.m: |- M = ( Monic1p ` R )


  assert |- ( ( R e. DivRing /\ I e. U /\ I =/= { .0. } ) -> ( ( G ` I ) e. I /\ ( G ` I ) e. M /\ ( D ` ( G ` I ) ) = inf ( ( D " ( I \ { .0. } ) ) , RR , < ) ) )

  proof
    cR
    cdr
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
    cI
    cG
    cfv
    #
    vg
    cv
    #
    cD
    cfv
    #
    cD
    cI
    @2
    cdif
    cima
    cr
    clt
    cinf
    #
    wceq
    #
    vg
    cI
    cM
    cin
    #
    crab
    #
    wcel
    #
    @5
    cI
    wcel
    #
    @5
    cM
    wcel
    #
    @5
    cD
    cfv
    #
    @8
    wceq
    #
    w3a
    #
    @4
    @5
    @9
    vg
    @10
    crio
    #
    @11
    @4
    @5
    cI
    @2
    wceq
    #
    c.0
    @18
    cif
    #
    @18
    @0
    @1
    @5
    @20
    wceq
    @3
    cD
    cP
    cR
    cU
    vg
    cG
    cI
    cM
    cdr
    c.0
    ig1pval.p
    ig1pval.g
    ig1pval3.z
    ig1pval3.u
    ig1pval3.d
    ig1pval3.m
    ig1pval
    3adant3
    @4
    @19
    c.0
    @18
    @4
    cI
    @2
    @0
    @1
    @3
    simp3
    neneqd
    iffalsed
    eqtrd
    @4
    @9
    vg
    @10
    wreu
    @18
    @11
    wcel
    cD
    cP
    cR
    cU
    vg
    cI
    cM
    c.0
    ig1pval.p
    ig1pval3.u
    ig1pval3.z
    ig1pval3.m
    ig1pval3.d
    ig1peu
    @9
    vg
    @10
    riotacl2
    syl
    eqeltrd
    @5
    @10
    wcel
    #
    @16
    wa
    @13
    @14
    wa
    #
    @16
    wa
    @12
    @17
    @21
    @22
    @16
    @5
    cI
    cM
    elin
    anbi1i
    @9
    @16
    vg
    @5
    @10
    @6
    @5
    wceq
    @7
    @15
    @8
    @6
    @5
    cD
    fveq2
    eqeq1d
    elrab
    @13
    @14
    @16
    df-3an
    3bitr4i
    sylib
end
