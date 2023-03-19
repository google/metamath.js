include "cif.mm"
include "wceq.mm"
include "wb.mm"
include "iftrue.mm"
include "eqcomd.mm"
include "syl.mm"
include "ibi.mm"
include "wn.mm"
include "iffalse.mm"
include "mpbii.mm"
include "pm2.61i.mm"

theorem elimhyp
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cA: class A
  let cB: class B
  assume elimhyp.1: |- ( A = if ( ph , A , B ) -> ( ph <-> ps ) )
  assume elimhyp.2: |- ( B = if ( ph , A , B ) -> ( ch <-> ps ) )
  assume elimhyp.3: |- ch


  assert |- ps

  proof
    wph
    wps
    wph
    wps
    wph
    cA
    wph
    cA
    cB
    cif
    #
    wceq
    wph
    wps
    wb
    wph
    @0
    cA
    wph
    cA
    cB
    iftrue
    eqcomd
    elimhyp.1
    syl
    ibi
    wph
    wn
    #
    wch
    wps
    elimhyp.3
    @1
    cB
    @0
    wceq
    wch
    wps
    wb
    @1
    @0
    cB
    wph
    cA
    cB
    iffalse
    eqcomd
    elimhyp.2
    syl
    mpbii
    pm2.61i
end
