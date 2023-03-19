include "crngcALTV.mm"
include "cfv.mm"
include "cresc.mm"
include "co.mm"
include "eqid.mm"
include "rhmsubcALTV.mm"
include "subccat.mm"

theorem rhmsubcALTVcat
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
  assume rngcrescrhmALTV.u: |- ( ph -> U e. V )
  assume rngcrescrhmALTV.c: |- C = ( RngCatALTV ` U )
  assume rngcrescrhmALTV.r: |- ( ph -> R = ( Ring i^i U ) )
  assume rngcrescrhmALTV.h: |- H = ( RingHom |` ( R X. R ) )


  assert |- ( ph -> ( ( RngCatALTV ` U ) |`cat H ) e. Cat )

  proof
    wph
    cU
    crngcALTV
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
    rngcrescrhmALTV.u
    rngcrescrhmALTV.c
    rngcrescrhmALTV.r
    rngcrescrhmALTV.h
    rhmsubcALTV
    subccat
end
