include "cmid.mm"
include "cfv.mm"
include "co.mm"
include "midcl.mm"
include "midbtwn.mm"
include "axtgbtwnid.mm"
include "eqcomd.mm"

theorem midid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let vm: setvar m
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  let cL: class L
  assume ismid.p: |- P = ( Base ` G )
  assume ismid.d: |- .- = ( dist ` G )
  assume ismid.i: |- I = ( Itv ` G )
  assume ismid.g: |- ( ph -> G e. TarskiG )
  assume ismid.1: |- ( ph -> G TarskiGDim>= 2 )
  assume midcl.1: |- ( ph -> A e. P )
  assume midcl.2: |- ( ph -> B e. P )


  assert |- ( ph -> ( A ( midG ` G ) A ) = A )

  proof
    wph
    cA
    cA
    cA
    cG
    cmid
    cfv
    co
    #
    wph
    cP
    cG
    cI
    c.mi
    cA
    @0
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    midcl.1
    wph
    cA
    cA
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    midcl.1
    midcl.1
    midcl
    wph
    cA
    cA
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    midcl.1
    midcl.1
    midbtwn
    axtgbtwnid
    eqcomd
end
