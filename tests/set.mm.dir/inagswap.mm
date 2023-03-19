include "cs3.mm"
include "cinag.mm"
include "cfv.mm"
include "wbr.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wa.mm"
include "wrex.mm"
include "cstrkg.mm"
include "isinag.mm"
include "mpbid.mm"
include "simpld.mm"
include "simp2d.mm"
include "simp1d.mm"
include "simp3d.mm"
include "3jca.mm"
include "simprd.mm"
include "cds.mm"
include "eqid.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "tgbtwncom.mm"
include "3expia.mm"
include "anim1d.mm"
include "reximdva.mm"
include "mpd.mm"
include "jca.mm"
include "mpbird.mm"

theorem inagswap
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  let cX: class X
  let vp: setvar p
  let vt: setvar t
  let vx: setvar x
  let vg: setvar g
  assume isinag.p: |- P = ( Base ` G )
  assume isinag.i: |- I = ( Itv ` G )
  assume isinag.k: |- K = ( hlG ` G )
  assume isinag.x: |- ( ph -> X e. P )
  assume isinag.a: |- ( ph -> A e. P )
  assume isinag.b: |- ( ph -> B e. P )
  assume isinag.c: |- ( ph -> C e. P )
  assume inagswap.g: |- ( ph -> G e. TarskiG )
  assume inagswap.1: |- ( ph -> X ( inA ` G ) <" A B C "> )


  assert |- ( ph -> X ( inA ` G ) <" C B A "> )

  proof
    wph
    cX
    cC
    cB
    cA
    cs3
    cG
    cinag
    cfv
    #
    wbr
    cC
    cB
    wne
    #
    cA
    cB
    wne
    #
    cX
    cB
    wne
    #
    w3a
    #
    vx
    cv
    #
    cC
    cA
    cI
    co
    wcel
    #
    @5
    cB
    wceq
    @5
    cX
    cB
    cK
    cfv
    wbr
    wo
    #
    wa
    #
    vx
    cP
    wrex
    #
    wa
    wph
    @4
    @9
    wph
    @1
    @2
    @3
    wph
    @2
    @1
    @3
    wph
    @2
    @1
    @3
    w3a
    #
    @5
    cA
    cC
    cI
    co
    wcel
    #
    @7
    wa
    #
    vx
    cP
    wrex
    #
    wph
    cX
    cA
    cB
    cC
    cs3
    @0
    wbr
    @10
    @13
    wa
    inagswap.1
    wph
    vx
    cA
    cB
    cC
    cP
    cG
    cI
    cK
    cstrkg
    cX
    isinag.p
    isinag.i
    isinag.k
    isinag.x
    isinag.a
    isinag.b
    isinag.c
    inagswap.g
    isinag
    mpbid
    #
    simpld
    #
    simp2d
    wph
    @2
    @1
    @3
    @15
    simp1d
    wph
    @2
    @1
    @3
    @15
    simp3d
    3jca
    wph
    @13
    @9
    wph
    @10
    @13
    @14
    simprd
    wph
    @12
    @8
    vx
    cP
    wph
    @5
    cP
    wcel
    #
    wa
    @11
    @6
    @7
    wph
    @16
    @11
    @6
    wph
    @16
    @11
    w3a
    cA
    @5
    cC
    cP
    cG
    cI
    cG
    cds
    cfv
    #
    isinag.p
    @17
    eqid
    isinag.i
    wph
    @16
    cG
    cstrkg
    wcel
    @11
    inagswap.g
    3ad2ant1
    wph
    @16
    cA
    cP
    wcel
    @11
    isinag.a
    3ad2ant1
    wph
    @16
    @11
    simp2
    wph
    @16
    cC
    cP
    wcel
    @11
    isinag.c
    3ad2ant1
    wph
    @16
    @11
    simp3
    tgbtwncom
    3expia
    anim1d
    reximdva
    mpd
    jca
    wph
    vx
    cC
    cB
    cA
    cP
    cG
    cI
    cK
    cstrkg
    cX
    isinag.p
    isinag.i
    isinag.k
    isinag.x
    isinag.c
    isinag.b
    isinag.a
    inagswap.g
    isinag
    mpbird
end
