include "cop.mm"
include "wcel.mm"
include "cfn.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "hashge0.mm"
include "adantl.mm"
include "0nn0.mm"
include "opfi1uzind.mm"
include "mpd3an3.mm"

theorem opfi1ind
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let ve: setvar e
  let vf: setvar f
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  assume opfi1ind.e: |- E e. _V
  assume opfi1ind.f: |- F e. _V
  assume opfi1ind.1: |- ( ( v = V /\ e = E ) -> ( ps <-> ph ) )
  assume opfi1ind.2: |- ( ( v = w /\ e = f ) -> ( ps <-> th ) )
  assume opfi1ind.3: |- ( ( <. v , e >. e. G /\ n e. v ) -> <. ( v \ { n } ) , F >. e. G )
  assume opfi1ind.4: |- ( ( w = ( v \ { n } ) /\ f = F ) -> ( th <-> ch ) )
  assume opfi1ind.base: |- ( ( <. v , e >. e. G /\ ( # ` v ) = 0 ) -> ps )
  assume opfi1ind.step: |- ( ( ( ( y + 1 ) e. NN0 /\ ( <. v , e >. e. G /\ ( # ` v ) = ( y + 1 ) /\ n e. v ) ) /\ ch ) -> ps )

  disjoint E e
  disjoint E n
  disjoint E v
  disjoint e n
  disjoint e v
  disjoint n v
  disjoint F f
  disjoint F w
  disjoint f w
  disjoint G e
  disjoint G f
  disjoint G n
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint e f
  disjoint e w
  disjoint e y
  disjoint f n
  disjoint f v
  disjoint f y
  disjoint n w
  disjoint n y
  disjoint v w
  disjoint v y
  disjoint w y
  disjoint V e
  disjoint V n
  disjoint V v
  disjoint f ps
  disjoint n ps
  disjoint ps w
  disjoint ps y
  disjoint e th
  disjoint n th
  disjoint th v
  disjoint ch f
  disjoint ch w
  disjoint e ph
  disjoint n ph
  disjoint ph v
  assert |- ( ( <. V , E >. e. G /\ V e. Fin ) -> ph )

  proof
    cV
    cE
    cop
    cG
    wcel
    #
    cV
    cfn
    wcel
    #
    cc0
    cV
    chash
    cfv
    cle
    wbr
    #
    wph
    @1
    @2
    @0
    cV
    cfn
    hashge0
    adantl
    wph
    wps
    wch
    wth
    vy
    vw
    vv
    ve
    vf
    vn
    cE
    cF
    cG
    cc0
    cV
    opfi1ind.e
    opfi1ind.f
    0nn0
    opfi1ind.1
    opfi1ind.2
    opfi1ind.3
    opfi1ind.4
    opfi1ind.base
    opfi1ind.step
    opfi1uzind
    mpd3an3
end
