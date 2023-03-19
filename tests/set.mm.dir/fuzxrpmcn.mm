include "cc.mm"
include "cxr.mm"
include "cvv.mm"
include "wcel.mm"
include "cnex.mm"
include "a1i.mm"
include "xrex.mm"
include "wss.mm"
include "uzsscn2.mm"
include "fpmd.mm"

theorem fuzxrpmcn
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume fuzxrpmcn.1: |- Z = ( ZZ>= ` M )
  assume fuzxrpmcn.2: |- ( ph -> F : Z --> RR* )


  assert |- ( ph -> F e. ( RR* ^pm CC ) )

  proof
    wph
    cc
    cxr
    cZ
    cF
    cvv
    cvv
    cc
    cvv
    wcel
    wph
    cnex
    a1i
    cxr
    cvv
    wcel
    wph
    xrex
    a1i
    cZ
    cc
    wss
    wph
    cM
    cZ
    fuzxrpmcn.1
    uzsscn2
    a1i
    fuzxrpmcn.2
    fpmd
end
