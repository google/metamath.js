include "cn.mm"
include "cin.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "inss1.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "inss2.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "zringlpirlem1.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "sseldi.mm"
include "syl5eqel.mm"

theorem zringlpirlem2
  let wph: wff ph
  let cG: class G
  let cI: class I
  let va: setvar a
  assume zringlpirlem.i: |- ( ph -> I e. ( LIdeal ` ZZring ) )
  assume zringlpirlem.n0: |- ( ph -> I =/= { 0 } )
  assume zringlpirlem.g: |- G = inf ( ( I i^i NN ) , RR , < )


  assert |- ( ph -> G e. I )

  proof
    wph
    cG
    cI
    cn
    cin
    #
    cr
    clt
    cinf
    #
    cI
    zringlpirlem.g
    wph
    @0
    cI
    @1
    cI
    cn
    inss1
    wph
    @0
    c1
    cuz
    cfv
    #
    wss
    @0
    c0
    wne
    @1
    @0
    wcel
    @0
    cn
    @2
    cI
    cn
    inss2
    nnuz
    sseqtri
    wph
    cI
    zringlpirlem.i
    zringlpirlem.n0
    zringlpirlem1
    @0
    c1
    infssuzcl
    sylancr
    sseldi
    syl5eqel
end
