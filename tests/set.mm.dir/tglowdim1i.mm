include "cv.mm"
include "wceq.mm"
include "wn.mm"
include "wrex.mm"
include "wne.mm"
include "wral.mm"
include "wa.mm"
include "cstrkg.mm"
include "wcel.mm"
include "adantr.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "tglowdim1.mm"
include "simpllr.mm"
include "simplr.mm"
include "eqeq2.mm"
include "rspccva.mm"
include "syl2anc.mm"
include "sylancom.mm"
include "eqtr3d.mm"
include "nne.mm"
include "sylibr.mm"
include "nrexdv.mm"
include "pm2.65da.mm"
include "rexnal.mm"
include "df-ne.mm"
include "rexbii.mm"

theorem tglowdim1i
  let wph: wff ph
  let vy: setvar y
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cX: class X
  let vx: setvar x
  let va: setvar a
  let vb: setvar b
  assume tglowdim1.p: |- P = ( Base ` G )
  assume tglowdim1.d: |- .- = ( dist ` G )
  assume tglowdim1.i: |- I = ( Itv ` G )
  assume tglowdim1.g: |- ( ph -> G e. TarskiG )
  assume tglowdim1.1: |- ( ph -> 2 <_ ( # ` P ) )
  assume tglowdim1i.1: |- ( ph -> X e. P )

  disjoint P y
  disjoint X y
  disjoint x y
  disjoint P x
  disjoint a b
  disjoint a y
  disjoint P a
  disjoint b y
  disjoint P b
  disjoint X a
  disjoint X b
  disjoint a ph
  disjoint b ph
  assert |- ( ph -> E. y e. P X =/= y )

  proof
    wph
    cX
    vy
    cv
    #
    wceq
    #
    wn
    #
    vy
    cP
    wrex
    #
    cX
    @0
    wne
    #
    vy
    cP
    wrex
    wph
    @1
    vy
    cP
    wral
    #
    wn
    @3
    wph
    @5
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    wph
    @5
    wa
    #
    va
    vb
    cP
    cG
    cI
    c.mi
    tglowdim1.p
    tglowdim1.d
    tglowdim1.i
    wph
    cG
    cstrkg
    wcel
    @5
    tglowdim1.g
    adantr
    wph
    c2
    cP
    chash
    cfv
    cle
    wbr
    @5
    tglowdim1.1
    adantr
    tglowdim1
    @10
    @9
    va
    cP
    @10
    @6
    cP
    wcel
    #
    wa
    #
    @8
    vb
    cP
    @12
    @7
    cP
    wcel
    #
    wa
    #
    @6
    @7
    wceq
    @8
    wn
    @14
    cX
    @6
    @7
    @14
    @5
    @11
    cX
    @6
    wceq
    #
    wph
    @5
    @11
    @13
    simpllr
    #
    @10
    @11
    @13
    simplr
    @1
    @15
    vy
    @6
    cP
    @0
    @6
    cX
    eqeq2
    rspccva
    syl2anc
    @12
    @13
    @5
    cX
    @7
    wceq
    #
    @16
    @1
    @17
    vy
    @7
    cP
    @0
    @7
    cX
    eqeq2
    rspccva
    sylancom
    eqtr3d
    @6
    @7
    nne
    sylibr
    nrexdv
    nrexdv
    pm2.65da
    @1
    vy
    cP
    rexnal
    sylibr
    @4
    @2
    vy
    cP
    cX
    @0
    df-ne
    rexbii
    sylibr
end
