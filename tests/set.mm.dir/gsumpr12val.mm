include "c1.mm"
include "c2.mm"
include "1zzd.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "df-2.mm"
include "a1i.mm"
include "gsumprval.mm"

theorem gsumpr12val
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cV: class V
  assume gsumpr12val.b: |- B = ( Base ` G )
  assume gsumpr12val.p: |- .+ = ( +g ` G )
  assume gsumpr12val.g: |- ( ph -> G e. V )
  assume gsumpr12val.f: |- ( ph -> F : { 1 , 2 } --> B )


  assert |- ( ph -> ( G gsum F ) = ( ( F ` 1 ) .+ ( F ` 2 ) ) )

  proof
    wph
    cB
    c.pl
    cF
    cG
    c1
    c2
    cV
    gsumpr12val.b
    gsumpr12val.p
    gsumpr12val.g
    wph
    1zzd
    c2
    c1
    c1
    caddc
    co
    wceq
    wph
    df-2
    a1i
    gsumpr12val.f
    gsumprval
end
