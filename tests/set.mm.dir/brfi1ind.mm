include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "hashge0.mm"
include "adantl.mm"
include "0nn0.mm"
include "brfi1uzind.mm"
include "mpd3an3.mm"

theorem brfi1ind
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
  assume brfi1ind.r: |- Rel G
  assume brfi1ind.f: |- F e. _V
  assume brfi1ind.1: |- ( ( v = V /\ e = E ) -> ( ps <-> ph ) )
  assume brfi1ind.2: |- ( ( v = w /\ e = f ) -> ( ps <-> th ) )
  assume brfi1ind.3: |- ( ( v G e /\ n e. v ) -> ( v \ { n } ) G F )
  assume brfi1ind.4: |- ( ( w = ( v \ { n } ) /\ f = F ) -> ( th <-> ch ) )
  assume brfi1ind.base: |- ( ( v G e /\ ( # ` v ) = 0 ) -> ps )
  assume brfi1ind.step: |- ( ( ( ( y + 1 ) e. NN0 /\ ( v G e /\ ( # ` v ) = ( y + 1 ) /\ n e. v ) ) /\ ch ) -> ps )

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
  assert |- ( ( V G E /\ V e. Fin ) -> ph )

  proof
    cV
    cE
    cG
    wbr
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
    brfi1ind.r
    brfi1ind.f
    0nn0
    brfi1ind.1
    brfi1ind.2
    brfi1ind.3
    brfi1ind.4
    brfi1ind.base
    brfi1ind.step
    brfi1uzind
    mpd3an3
end
