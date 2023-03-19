include "sb4b.mm"

theorem wl-sb6nae
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( -. A. x x = y -> ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) )

  proof
    wph
    vx
    vy
    sb4b
end
