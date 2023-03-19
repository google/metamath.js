include "wa.mm"
include "wb.mm"
include "cif.mm"
include "wceq.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "syl.mm"
include "adantl.mm"
include "mpbid.mm"
include "wn.mm"
include "iffalse.mm"
include "pm2.61dan.mm"

theorem ifbothda
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wet: wff et
  let cA: class A
  let cB: class B
  assume ifboth.1: |- ( A = if ( ph , A , B ) -> ( ps <-> th ) )
  assume ifboth.2: |- ( B = if ( ph , A , B ) -> ( ch <-> th ) )
  assume ifbothda.3: |- ( ( et /\ ph ) -> ps )
  assume ifbothda.4: |- ( ( et /\ -. ph ) -> ch )


  assert |- ( et -> th )

  proof
    wet
    wph
    wth
    wet
    wph
    wa
    wps
    wth
    ifbothda.3
    wph
    wps
    wth
    wb
    #
    wet
    wph
    cA
    wph
    cA
    cB
    cif
    #
    wceq
    @0
    wph
    @1
    cA
    wph
    cA
    cB
    iftrue
    eqcomd
    ifboth.1
    syl
    adantl
    mpbid
    wet
    wph
    wn
    #
    wa
    wch
    wth
    ifbothda.4
    @2
    wch
    wth
    wb
    #
    wet
    @2
    cB
    @1
    wceq
    @3
    @2
    @1
    cB
    wph
    cA
    cB
    iffalse
    eqcomd
    ifboth.2
    syl
    adantl
    mpbid
    pm2.61dan
end
