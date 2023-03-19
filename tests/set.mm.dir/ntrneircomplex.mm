include "cdif.mm"
include "cvv.mm"
include "ntrneibex.mm"
include "difssd.mm"
include "sselpwd.mm"

theorem ntrneircomplex
  let wph: wff ph
  let cB: class B
  let cS: class S
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

  disjoint i j
  disjoint i k
  disjoint j k
  disjoint i l
  disjoint j l
  disjoint i m
  disjoint j m
  assert |- ( ph -> ( B \ S ) e. ~P B )

  proof
    wph
    cB
    cS
    cdif
    cB
    cvv
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
    wph
    cB
    cS
    difssd
    sselpwd
end
