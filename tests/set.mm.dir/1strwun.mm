include "cnx.mm"
include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "wunndx.mm"
include "wunstr.mm"
include "1strwunbndx.mm"

theorem 1strwun
  let wph: wff ph
  let cB: class B
  let cU: class U
  let cG: class G
  assume 1str.g: |- G = { <. ( Base ` ndx ) , B >. }
  assume 1strwun.u: |- ( ph -> U e. WUni )
  assume 1strwun.o: |- ( ph -> _om e. U )


  assert |- ( ( ph /\ B e. U ) -> G e. U )

  proof
    wph
    cB
    cU
    cG
    1str.g
    1strwun.u
    wph
    cnx
    cU
    cbs
    c1
    df-base
    1strwun.u
    wph
    cU
    1strwun.u
    1strwun.o
    wunndx
    wunstr
    1strwunbndx
end
