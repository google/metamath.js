include "cpw.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "ntrneibex.mm"
include "pwexg.mm"
include "syl.mm"
include "eqid.mm"
include "fsovcnvd.mm"

theorem ntrneicnv
  let wph: wff ph
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cI: class I
  let cN: class N
  let cO: class O
  let vl: setvar l
  assume ntrnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume ntrnei.f: |- F = ( ~P B O B )
  assume ntrnei.r: |- ( ph -> I F N )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  assert |- ( ph -> `' F = ( B O ~P B ) )

  proof
    wph
    vm
    vl
    cB
    cpw
    #
    cB
    vk
    cF
    cB
    @0
    cO
    co
    #
    cO
    cvv
    cvv
    vi
    vj
    ntrnei.o
    wph
    cB
    cvv
    wcel
    @0
    cvv
    wcel
    wph
    cB
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    vl
    ntrnei.o
    ntrnei.f
    ntrnei.r
    ntrneibex
    #
    cB
    cvv
    pwexg
    syl
    @2
    ntrnei.f
    @1
    eqid
    fsovcnvd
end
