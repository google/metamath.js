include "cn.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "wcel.mm"
include "pm3.24.mm"
include "clt.mm"
include "cr.mm"
include "wb.mm"
include "nnre.mm"
include "lenlt.mm"
include "syl2an.mm"
include "imbi2d.mm"
include "con34b.mm"
include "syl6bbr.mm"
include "ralbidva.mm"
include "sylbid.mm"
include "anim2d.mm"
include "ancom.mm"
include "syl6ib.mm"
include "mtoi.mm"
include "nrex.mm"
include "weq.mm"
include "notbid.mm"
include "nnwos.mm"
include "mto.mm"
include "dfral2.mm"
include "mpbir.mm"
include "rspec.mm"

theorem indstr
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume indstr.1: |- ( x = y -> ( ph <-> ps ) )
  assume indstr.2: |- ( x e. NN -> ( A. y e. NN ( y < x -> ps ) -> ph ) )

  disjoint x y
  disjoint ph y
  disjoint ps x
  assert |- ( x e. NN -> ph )

  proof
    wph
    vx
    cn
    wph
    vx
    cn
    wral
    wph
    wn
    #
    vx
    cn
    wrex
    #
    wn
    @1
    @0
    wps
    wn
    #
    vx
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    wi
    #
    vy
    cn
    wral
    #
    wa
    #
    vx
    cn
    wrex
    @8
    vx
    cn
    @3
    cn
    wcel
    #
    @8
    wph
    @0
    wa
    #
    wph
    pm3.24
    @9
    @8
    @0
    wph
    wa
    @10
    @9
    @7
    wph
    @0
    @9
    @7
    @4
    @3
    clt
    wbr
    #
    wps
    wi
    #
    vy
    cn
    wral
    wph
    @9
    @6
    @12
    vy
    cn
    @9
    @4
    cn
    wcel
    #
    wa
    #
    @6
    @2
    @11
    wn
    #
    wi
    @12
    @14
    @5
    @15
    @2
    @9
    @3
    cr
    wcel
    @4
    cr
    wcel
    @5
    @15
    wb
    @13
    @3
    nnre
    @4
    nnre
    @3
    @4
    lenlt
    syl2an
    imbi2d
    @11
    wps
    con34b
    syl6bbr
    ralbidva
    indstr.2
    sylbid
    anim2d
    @0
    wph
    ancom
    syl6ib
    mtoi
    nrex
    @0
    @2
    vx
    vy
    vx
    vy
    weq
    wph
    wps
    indstr.1
    notbid
    nnwos
    mto
    wph
    vx
    cn
    dfral2
    mpbir
    rspec
end
