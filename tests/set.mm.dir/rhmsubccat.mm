include "crngc.mm"
include "cfv.mm"
include "cresc.mm"
include "co.mm"
include "eqid.mm"
include "rhmsubc.mm"
include "subccat.mm"

theorem rhmsubccat
  let wph: wff ph
  let cC: class C
  let cR: class R
  let cU: class U
  let cH: class H
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  assume rngcrescrhm.u: |- ( ph -> U e. V )
  assume rngcrescrhm.c: |- C = ( RngCat ` U )
  assume rngcrescrhm.r: |- ( ph -> R = ( Ring i^i U ) )
  assume rngcrescrhm.h: |- H = ( RingHom |` ( R X. R ) )


  assert |- ( ph -> ( ( RngCat ` U ) |`cat H ) e. Cat )

  proof
    wph
    cU
    crngc
    cfv
    #
    @0
    cH
    cresc
    co
    #
    cH
    @1
    eqid
    wph
    cC
    cR
    cU
    cH
    cV
    rngcrescrhm.u
    rngcrescrhm.c
    rngcrescrhm.r
    rngcrescrhm.h
    rhmsubc
    subccat
end
