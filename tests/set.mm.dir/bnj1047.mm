include "cv.mm"
include "cep.mm"
include "wbr.mm"
include "wsbc.mm"
include "wi.mm"
include "wral.mm"
include "imbi2i.mm"
include "ralbii.mm"
include "bitr4i.mm"

theorem bnj1047
  let wet: wff et
  let wrh: wff rh
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let bnjwetm: wff et'
  assume bnj1047.1: |- ( rh <-> A. j e. n ( j _E i -> [. j / i ]. et ) )
  assume bnj1047.2: |- ( et' <-> [. j / i ]. et )


  assert |- ( rh <-> A. j e. n ( j _E i -> et' ) )

  proof
    wrh
    vj
    cv
    #
    vi
    cv
    cep
    wbr
    #
    wet
    vi
    @0
    wsbc
    #
    wi
    #
    vj
    vn
    cv
    #
    wral
    @1
    bnjwetm
    wi
    #
    vj
    @4
    wral
    bnj1047.1
    @5
    @3
    vj
    @4
    bnjwetm
    @2
    @1
    bnj1047.2
    imbi2i
    ralbii
    bitr4i
end
