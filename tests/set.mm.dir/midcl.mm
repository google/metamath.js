include "cmid.mm"
include "cfv.mm"
include "midf.mm"
include "fovrnd.mm"

theorem midcl
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


  assert |- ( ph -> ( A ( midG ` G ) B ) e. P )

  proof
    wph
    cA
    cB
    cP
    cP
    cP
    cG
    cmid
    cfv
    wph
    cP
    cG
    cI
    c.mi
    ismid.p
    ismid.d
    ismid.i
    ismid.g
    ismid.1
    midf
    midcl.1
    midcl.2
    fovrnd
end
