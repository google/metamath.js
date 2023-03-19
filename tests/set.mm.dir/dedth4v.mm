include "wa.mm"
include "dedth4h.mm"
include "anidms.mm"

theorem dedth4v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  assume dedth4v.1: |- ( A = if ( ph , A , R ) -> ( ps <-> ch ) )
  assume dedth4v.2: |- ( B = if ( ph , B , S ) -> ( ch <-> th ) )
  assume dedth4v.3: |- ( C = if ( ph , C , T ) -> ( th <-> ta ) )
  assume dedth4v.4: |- ( D = if ( ph , D , U ) -> ( ta <-> et ) )
  assume dedth4v.5: |- et


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wph
    wph
    wa
    wps
    wph
    wph
    wph
    wph
    wps
    wch
    wth
    wta
    wet
    cA
    cB
    cC
    cD
    cR
    cS
    cT
    cU
    dedth4v.1
    dedth4v.2
    dedth4v.3
    dedth4v.4
    dedth4v.5
    dedth4h
    anidms
    anidms
end
